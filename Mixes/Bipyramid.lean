import Mixes.Defs
import Mixes.Means

/-!
# Section 19: densities with a concave root, the levels of the bipyramids, reductions

* `Mixes.Bipyramid.beta_le` and `Mixes.Bipyramid.pconc` (Theorem 67, `o:thm:pconc`): along
  the peeling of a density `f = g ^ p` with `g` concave, `β(U) ≤ p + 2`; with Theorems 34 and 36
  (`c:thm:peel`, `c:thm:mix`) taken as explicit hypotheses this gives complete mixability for
  every `n ≥ p + 2`. `pconc_sharp`: the mean of `(p + 1)(1 - x)^p` is `1/(p + 2)`.
* `Mixes.Bipyramid.levels` (Lemma 69, `o:lem:levels`): the density `α` of the largest level, the
  identity `α + 2b = 3ν` (`key_identity`, via the fundamental theorem of calculus for absolutely
  continuous functions), and the `3`-complete mix `levelMix` of the levels of the bipyramids.
* `Mixes.Bipyramid.reduce_c` and `Mixes.Bipyramid.reduce_c2` (Proposition 71(c),
  `o:prop:reduce`): the reformulation of `(d+1)`-complete mixability of `U(K)` through the mean of
  `d` uniform points, and for `d = 2` through kernels symmetric about their base point.
-/

open Set MeasureTheory intervalIntegral ProbabilityTheory

noncomputable section

namespace Mixes

namespace Bipyramid

/-! ## Theorem 67 -/

section PConc

/-- The core of **Theorem 67** (`o:thm:pconc`): if `g ≥ 0` is concave and continuous on
`[A, B]`, `p ≥ 1`, `0 ≤ U ≤ g ^ p` on `[A, B]`, `A < μ < B`, `g(μ) ^ p > U`, and `g ^ p - U` has
mean `μ` on `[A, B]`, then `μ - A` and `B - μ` are both at least `(B - A) / (p + 2)`. -/
theorem beta_le {p U A B μ : ℝ} {g : ℝ → ℝ} (hp : 1 ≤ p) (hU : 0 ≤ U)
    (hg : ConcaveOn ℝ (Icc A B) g) (hgc : ContinuousOn g (Icc A B))
    (hg0 : ∀ x ∈ Icc A B, 0 ≤ g x) (hgU : ∀ x ∈ Icc A B, U ≤ g x ^ p)
    (hμ : μ ∈ Ioo A B) (hpos : U < g μ ^ p)
    (hmean : ∫ x in A..B, (x - μ) * (g x ^ p - U) = 0) :
    (B - A) / (p + 2) ≤ μ - A ∧ (B - A) / (p + 2) ≤ B - μ := by
  have hp0 : 0 < p := by linarith
  have hAB : A < B := hμ.1.trans hμ.2
  set h : ℝ → ℝ := fun x => (g x ^ p - U) ^ (1 / p) with hh
  have hconc : ConcaveOn ℝ (Icc A B) h := Mixes.root_comp_concaveOn hp hU hg hg0 hgU
  have hpow : ∀ x ∈ Icc A B, h x ^ p = g x ^ p - U := fun x hx => by
    simp only [hh, one_div]
    exact Real.rpow_inv_rpow (sub_nonneg.2 (hgU x hx)) hp0.ne'
  have hh0 : ∀ x ∈ Icc A B, 0 ≤ h x := fun x _ => Real.rpow_nonneg (by
    exact sub_nonneg.2 (hgU x ‹_›)) _
  have hμI : μ ∈ Icc A B := Ioo_subset_Icc_self hμ
  have hhμ : 0 < h μ := Real.rpow_pos_of_pos (sub_pos.2 hpos) _
  have hne : ∃ x ∈ Icc A B, h x ≠ 0 := ⟨μ, hμI, hhμ.ne'⟩
  have hm := Mixes.root_mean hp0.le hAB hconc hh0 hne
  -- the density `f = g ^ p - U`
  set f : ℝ → ℝ := fun x => g x ^ p - U with hf
  have hfc : ContinuousOn f (Icc A B) :=
    (hgc.rpow_const fun x hx => Or.inr hp0.le).sub continuousOn_const
  have hfi : IntervalIntegrable f volume A B :=
    (hfc.mono (by rw [uIcc_of_le hAB.le])).intervalIntegrable
  have hxfi : IntervalIntegrable (fun x => x * f x) volume A B :=
    ((continuousOn_id.mul hfc).mono (by rw [uIcc_of_le hAB.le])).intervalIntegrable
  -- positivity of `h` on `(A, B)`
  have hhpos : ∀ x ∈ Ioo A B, 0 < h x := by
    intro x hx
    rcases le_total x μ with hxμ | hxμ
    · -- `x = s A + (1 - s) μ`
      set s := (μ - x) / (μ - A)
      have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith [hμ.1])
      have hs1 : s < 1 := (div_lt_one (by linarith [hμ.1])).2 (by linarith [hx.1])
      have hx' : s • A + (1 - s) • μ = x := by
        have : s * (μ - A) = μ - x := div_mul_cancel₀ _ (by linarith [hμ.1])
        simp only [smul_eq_mul]; linear_combination -this
      have := hconc.2 (left_mem_Icc.2 hAB.le) hμI hs0 (show (0:ℝ) ≤ 1 - s by linarith) (by ring)
      rw [hx'] at this
      simp only [smul_eq_mul] at this
      nlinarith [hh0 A (left_mem_Icc.2 hAB.le)]
    · set s := (x - μ) / (B - μ)
      have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith [hμ.2])
      have hs1 : s < 1 := (div_lt_one (by linarith [hμ.2])).2 (by linarith [hx.2])
      have hx' : s • B + (1 - s) • μ = x := by
        have : s * (B - μ) = x - μ := div_mul_cancel₀ _ (by linarith [hμ.2])
        simp only [smul_eq_mul]; linear_combination this
      have := hconc.2 (right_mem_Icc.2 hAB.le) hμI hs0 (show (0:ℝ) ≤ 1 - s by linarith) (by ring)
      rw [hx'] at this
      simp only [smul_eq_mul] at this
      nlinarith [hh0 B (right_mem_Icc.2 hAB.le)]
  have hIpos : 0 < ∫ x in A..B, f x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hfi (fun x hx => ?_) hAB
    have := hpow x (Ioo_subset_Icc_self hx)
    simp only [hf]
    rw [← this]
    exact Real.rpow_pos_of_pos (hhpos x hx) _
  -- the mean equals `μ`
  have hsplit : ∫ x in A..B, (x - μ) * f x = (∫ x in A..B, x * f x) - μ * ∫ x in A..B, f x := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hxfi
      (hfi.const_mul μ)]
    congr 1; ext x; ring
  have hmeanμ : meanOn A B (fun x => h x ^ p) = μ := by
    unfold meanOn
    have e1 : ∫ x in A..B, h x ^ p = ∫ x in A..B, f x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hAB.le] at hx; exact hpow x hx
    have e2 : ∫ x in A..B, x * h x ^ p = ∫ x in A..B, x * f x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hAB.le] at hx; simp only [hpow x hx, hf]
    rw [e1, e2, div_eq_iff hIpos.ne']
    have := hsplit
    simp only [hf] at this hmean
    linarith
  rw [hmeanμ] at hm
  exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- The ratio `β = (ℓ + r) / min(ℓ, r)` with `ℓ = μ - A` and `r = B - μ`. -/
def beta (μ A B : ℝ) : ℝ := ((μ - A) + (B - μ)) / min (μ - A) (B - μ)

/-- `β(U) ≤ p + 2` from the two bounds of `beta_le`. -/
lemma beta_le_of {p A B μ : ℝ} (hp : 0 < p) (hμ : μ ∈ Ioo A B)
    (h1 : (B - A) / (p + 2) ≤ μ - A) (h2 : (B - A) / (p + 2) ≤ B - μ) :
    beta μ A B ≤ p + 2 := by
  unfold beta
  have hm : 0 < min (μ - A) (B - μ) := lt_min (by linarith [hμ.1]) (by linarith [hμ.2])
  rw [div_le_iff₀ hm]
  have h := le_min h1 h2
  rw [div_le_iff₀ (by linarith)] at h
  nlinarith

/-- Theorem 34 (`c:thm:peel`), parts (a) and (b), as used in Theorem 67: the ends `A(U)`,
`B(U)` of the peeling of the density `f` with mean `μ` satisfy, for `0 ≤ U < f(μ)`,
`0 ≤ A(U) < μ < B(U) ≤ 1`, `f ≥ U` on `[A(U), B(U)]`, and `f - U` has mean `μ` on
`[A(U), B(U)]`. This is a hypothesis (the peeling is not formalised here). -/
def PeelingProps (f : ℝ → ℝ) (μ : ℝ) (A B : ℝ → ℝ) : Prop :=
  ∀ U, 0 ≤ U → U < f μ → 0 ≤ A U ∧ A U < μ ∧ μ < B U ∧ B U ≤ 1 ∧
    (∀ x ∈ Icc (A U) (B U), U ≤ f x) ∧ ∫ x in A U..B U, (x - μ) * (f x - U) = 0

/-- The distribution with density `f` on `[0, 1]`. -/
def densityOn01 (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0:ℝ) 1)).withDensity fun x => ENNReal.ofReal (f x)

/-- **Theorem 67** (`o:thm:pconc`), on `[0, 1]`. Let `p ≥ 1`, and let `f = g ^ p` be a
probability density on `[0, 1]` with mean `μ`, where `g ≥ 0` is concave and continuous on
`[0, 1]`. Let `A`, `B` be the ends of the peeling of `f` (Theorem 34, hypothesis `H34`), and assume
Theorem 36 (`c:thm:mix`) for `f` (hypothesis `H36`: if `n ≥ 3` and `β(U) ≤ n` for all
`0 ≤ U < f(μ)`, then `f` is `n`-completely mixable). Then `f` is `n`-completely mixable for every
integer `n ≥ p + 2`. -/
theorem pconc {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Icc 0 1) g)
    (hgc : ContinuousOn g (Icc 0 1)) (hg0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) (μ : ℝ)
    (_hdens : ∫ x in (0:ℝ)..1, g x ^ p = 1) (_hμ : μ = ∫ x in (0:ℝ)..1, x * g x ^ p)
    (A B : ℝ → ℝ) (H34 : PeelingProps (fun x => g x ^ p) μ A B)
    (H36 : ∀ n : ℕ, 3 ≤ n → (∀ U, 0 ≤ U → U < g μ ^ p → beta μ (A U) (B U) ≤ n) →
      CompletelyMixable n (densityOn01 fun x => g x ^ p)) :
    ∀ n : ℕ, p + 2 ≤ n → CompletelyMixable n (densityOn01 fun x => g x ^ p) := by
  intro n hn
  have hn3 : (3:ℝ) ≤ n := by linarith
  refine H36 n (by exact_mod_cast hn3) fun U hU hUμ => ?_
  obtain ⟨hA0, hAμ, hμB, hB1, hfU, hmean⟩ := H34 U hU hUμ
  have sub : Icc (A U) (B U) ⊆ Icc 0 1 := Icc_subset_Icc hA0 hB1
  have hμI : μ ∈ Ioo (A U) (B U) := ⟨hAμ, hμB⟩
  obtain ⟨h1, h2⟩ := beta_le hp hU (hg.subset sub (convex_Icc _ _)) (hgc.mono sub)
    (fun x hx => hg0 x (sub hx)) hfU hμI hUμ hmean
  exact (beta_le_of (by linarith) hμI h1 h2).trans hn

/-- Sharpness in **Theorem 67**: the density `(p + 1)(1 - x)^p` on `[0, 1]` has mean
`1 / (p + 2)`. -/
theorem pconc_sharp {p : ℝ} (hp : 0 ≤ p) :
    ∫ x in (0:ℝ)..1, x * ((p + 1) * (1 - x) ^ p) = 1 / (p + 2) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (1 - u) * ((p + 1) * u ^ p)) (a := 0) (b := 1) 1
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  rw [h]
  have e : (fun u : ℝ => (1 - u) * ((p + 1) * u ^ p)) =
      fun u => (p + 1) * u ^ p - (p + 1) * u ^ (p + 1) := by
    ext u
    by_cases hu : u = 0
    · subst hu; simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]
    · rw [Real.rpow_add_one hu]; ring
  rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    integral_rpow (Or.inl (by linarith))]
  · simp only [Real.one_rpow]
    rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    field_simp
    ring
  · exact (intervalIntegrable_rpow' (by linarith)).const_mul _
  · exact (intervalIntegrable_rpow' (by linarith)).const_mul _

end PConc

/-! ## Lemma 69: the levels of the bipyramids -/

section Levels

/-- The hypotheses of **Lemma 69** (`o:lem:levels`) on `ν`: a probability density on `[0, 1]`,
non-increasing and absolutely continuous on `[0, 1]`, Lipschitz on `[0, 1/2]`, `ν(1) = 0`,
`∫_{1/2}^1 ν(a)/(1-a) da < ∞` and condition (17), `ν(1/2) ≥ 2 ∫_{1/2}^1 ν(a)/(1-a) da`. -/
structure LevelHyp (ν : ℝ → ℝ) : Prop where
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ ν x
  int_one : ∫ x in (0:ℝ)..1, ν x = 1
  anti : AntitoneOn ν (Icc 0 1)
  ac : AbsolutelyContinuousOnInterval ν 0 1
  lip : ∃ K, LipschitzOnWith K ν (Icc 0 (1 / 2))
  one : ν 1 = 0
  fin : IntegrableOn (fun a => ν a / (1 - a)) (Icc (1 / 2) 1)
  star : 2 * ∫ a in (1 / 2 : ℝ)..1, ν a / (1 - a) ≤ ν (1 / 2)

variable (ν : ℝ → ℝ)

/-- `∫_{1/2}^1 ν(a)/(1-a) da`. -/
def I1 : ℝ := ∫ a in (1 / 2 : ℝ)..1, ν a / (1 - a)

/-- `α₀ = 3 ν(1/2) - 6 ∫_{1/2}^1 ν(a)/(1-a) da`. -/
def alpha0 : ℝ := 3 * ν (1 / 2) - 6 * I1 ν

/-- The integrand `(-3 ν'(t) + 6 ν(t + 1/2)/(1/2 - t)) / t²` in the definition of `α`. -/
def gInt (t : ℝ) : ℝ := (-3 * deriv ν t + 6 * (ν (t + 1 / 2) / (1 / 2 - t))) / t ^ 2

/-- The formula `x² (4 α₀ + ∫_x^{1/2} gInt)` for `α` on `(0, 1/2]`. -/
def alphaF (x : ℝ) : ℝ := x ^ 2 * (4 * alpha0 ν + ∫ t in x..(1 / 2), gInt ν t)

/-- The density `α` of the largest level `A` in Lemma 69 (zero outside `(0, 1]`). -/
def alpha (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 / 2 then alphaF ν x else if x ≤ 1 then 3 * ν x else 0

/-- The function `b` of the proof of Lemma 69, the density of `B` and of `C` on `[0, 1/2]`. -/
def bfun (x : ℝ) : ℝ :=
  (∫ a in x..(1 / 2), alpha ν a / a) + ∫ a in (1 / 2 : ℝ)..(x + 1 / 2), 3 * ν a / (1 - a)

variable {ν}

lemma alpha_of_mem {x : ℝ} (hx : x ∈ Ioc (0:ℝ) (1 / 2)) : alpha ν x = alphaF ν x := by
  unfold alpha; split_ifs <;> first | rfl | (exfalso; linarith [hx.1, hx.2])

lemma alpha_of_mem' {x : ℝ} (hx : x ∈ Ioc (1 / 2 : ℝ) 1) : alpha ν x = 3 * ν x := by
  unfold alpha; split_ifs <;> first | rfl | (exfalso; linarith [hx.1, hx.2])

lemma q_intervalIntegrable (h : LevelHyp ν) :
    IntervalIntegrable (fun t => ν (t + 1 / 2) / (1 / 2 - t)) volume 0 (1 / 2) := by
  have h1 : IntervalIntegrable (fun a => ν a / (1 - a)) volume (1 / 2) 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 h.fin
  have h2 := h1.comp_add_right (1 / 2)
  norm_num at h2
  convert h2 using 2 with t
  ring_nf

lemma deriv_nonpos (h : LevelHyp ν) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : deriv ν t ≤ 0 := by
  have := h.anti.derivWithin_nonpos (x := t)
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at this

lemma gInt_nonneg (h : LevelHyp ν) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) (1 / 2)) : 0 ≤ gInt ν t := by
  unfold gInt
  have h1 := deriv_nonpos h ⟨ht.1, by linarith [ht.2]⟩
  have h2 : 0 ≤ ν (t + 1 / 2) := h.nonneg _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h3 : 0 ≤ ν (t + 1 / 2) / (1 / 2 - t) := div_nonneg h2 (by linarith [ht.2])
  exact div_nonneg (by linarith) (by positivity)

lemma gInt_intervalIntegrable (h : LevelHyp ν) {x0 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ 1 / 2) :
    IntervalIntegrable (gInt ν) volume x0 (1 / 2) := by
  have hsub : uIcc x0 (1 / 2) ⊆ uIcc 0 (1 / 2) := by
    rw [uIcc_of_le hx, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc hx0.le le_rfl
  have hd : IntervalIntegrable (deriv ν) volume x0 (1 / 2) :=
    h.ac.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le hx, uIcc_of_le (by norm_num)]
      exact Icc_subset_Icc hx0.le (by norm_num))
  have hq := (q_intervalIntegrable h).mono_set hsub
  have hnum := (hd.const_mul (-3)).add (hq.const_mul 6)
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc x0 (1 / 2)) := by
    refine (continuousOn_pow 2).inv₀ fun t ht => ?_
    rw [uIcc_of_le hx] at ht
    exact pow_ne_zero _ (by linarith [ht.1])
  have := hnum.mul_continuousOn hc
  refine this.congr fun t _ => ?_
  simp [gInt, div_eq_mul_inv]

lemma alpha0_nonneg (h : LevelHyp ν) : 0 ≤ alpha0 ν := by
  have := h.star; unfold alpha0 I1; linarith

lemma alphaF_nonneg (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) (1 / 2)) :
    0 ≤ alphaF ν x := by
  unfold alphaF
  have hG : 0 ≤ ∫ t in x..(1 / 2), gInt ν t :=
    intervalIntegral.integral_nonneg hx.2 fun t ht => gInt_nonneg h ⟨by linarith [hx.1, ht.1], ht.2⟩
  have := alpha0_nonneg h
  positivity

/-- `α ≥ 0` (Lemma 69). -/
theorem alpha_nonneg (h : LevelHyp ν) (x : ℝ) : 0 ≤ alpha ν x := by
  unfold alpha
  split_ifs with h0 h1 h2
  · exact le_rfl
  · exact alphaF_nonneg h ⟨not_le.1 h0, h1⟩
  · have := h.nonneg x ⟨by linarith, h2⟩; linarith
  · exact le_rfl

/-- `t ↦ 3 ν(t + 1/2) / (1/2 - t)`, the second part of `b` after the shift `a = t + 1/2`. -/
def qq (ν : ℝ → ℝ) (t : ℝ) : ℝ := 3 * (ν (t + 1 / 2) / (1 / 2 - t))

lemma qq_intervalIntegrable (h : LevelHyp ν) : IntervalIntegrable (qq ν) volume 0 (1 / 2) :=
  (q_intervalIntegrable h).const_mul 3

lemma Q_eq (y : ℝ) :
    ∫ a in (1 / 2 : ℝ)..(y + 1 / 2), 3 * ν a / (1 - a) = ∫ t in (0:ℝ)..y, qq ν t := by
  have := intervalIntegral.integral_comp_add_right (fun a => 3 * ν a / (1 - a)) (a := 0) (b := y)
    (1 / 2)
  simp only [zero_add] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [qq]
  rw [show (1:ℝ) - (t + 1 / 2) = 1 / 2 - t by ring, mul_div_assoc]

lemma bfun_half : bfun ν (1 / 2) = 3 * I1 ν := by
  unfold bfun I1
  rw [intervalIntegral.integral_same, zero_add, ← intervalIntegral.integral_const_mul]
  norm_num [mul_div_assoc]

lemma alphaF_half : alphaF ν (1 / 2) = alpha0 ν := by
  unfold alphaF; rw [intervalIntegral.integral_same]; ring


lemma alphaF_ac (h : LevelHyp ν) {x0 : ℝ} (hx0 : 0 < x0) (hx1 : x0 ≤ 1 / 2) :
    AbsolutelyContinuousOnInterval (alphaF ν) x0 (1 / 2) := by
  have hhalf : (1 / 2 : ℝ) ∈ uIcc x0 (1 / 2) := right_mem_uIcc
  have hg := gInt_intervalIntegrable h hx0 hx1
  have hG_ac :
      AbsolutelyContinuousOnInterval (fun y => ∫ t in y..(1 / 2), gInt ν t) x0 (1 / 2) := by
    have := (hg.absolutelyContinuousOnInterval_intervalIntegral hhalf).fun_neg
    refine this.congr fun y _ => ?_
    simp only
    rw [intervalIntegral.integral_symm, neg_neg]
  have h1 : AbsolutelyContinuousOnInterval (fun y : ℝ => y ^ 2) x0 (1 / 2) :=
    (contDiff_id.pow 2).contDiffOn.absolutelyContinuousOnInterval
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => 4 * alpha0 ν) x0 (1 / 2) :=
    contDiffOn_const.absolutelyContinuousOnInterval
  exact h1.fun_mul (h2.fun_add hG_ac)

/-- The identity `α + 2 b = 3 ν` on `(0, 1/2]` of the proof of **Lemma 69**: both sides are
absolutely continuous on `[x₀, 1/2]` with the same derivative almost everywhere, and they agree at
`1/2` by the definition of `α₀`. -/
theorem key_identity (h : LevelHyp ν) {x0 : ℝ} (hx : x0 ∈ Ioc (0:ℝ) (1 / 2)) :
    alpha ν x0 + 2 * bfun ν x0 = 3 * ν x0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hI : uIcc x0 (1 / 2) = Icc x0 (1 / 2) := uIcc_of_le hx1
  have hhalf : (1 / 2 : ℝ) ∈ uIcc x0 (1 / 2) := right_mem_uIcc
  have hg := gInt_intervalIntegrable h hx0 hx1
  have hA_ac := alphaF_ac h hx0 hx1
  -- the integral `P`
  have hP_cont : ContinuousOn (fun a => alpha ν a / a) (uIcc x0 (1 / 2)) := by
    refine (hA_ac.continuousOn.div continuousOn_id fun a ha => ?_).congr fun a ha => ?_
    · rw [hI] at ha; simp only [id]; linarith [ha.1]
    · rw [hI] at ha
      simp only [alpha_of_mem ⟨hx0.trans_le ha.1, ha.2⟩, Pi.div_apply, id]
  have hP_int : IntervalIntegrable (fun a => alpha ν a / a) volume x0 (1 / 2) :=
    hP_cont.intervalIntegrable
  have hP_ac : AbsolutelyContinuousOnInterval (fun y => ∫ a in y..(1 / 2), alpha ν a / a)
      x0 (1 / 2) := by
    have := (hP_int.absolutelyContinuousOnInterval_intervalIntegral hhalf).fun_neg
    refine this.congr fun y _ => ?_
    simp only
    rw [intervalIntegral.integral_symm, neg_neg]
  -- the integral `Q`
  have hqq := qq_intervalIntegrable h
  have hsub : uIcc x0 (1 / 2) ⊆ uIcc 0 (1 / 2) := by
    rw [hI, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc hx0.le le_rfl
  have hQ_ac : AbsolutelyContinuousOnInterval
      (fun y => ∫ a in (1 / 2 : ℝ)..(y + 1 / 2), 3 * ν a / (1 - a)) x0 (1 / 2) := by
    have := (hqq.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).mono hsub
    exact this.congr fun y _ => (Q_eq y).symm
  have hν_ac : AbsolutelyContinuousOnInterval ν x0 (1 / 2) :=
    h.ac.mono (by rw [hI, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc hx0.le (by norm_num))
  set H : ℝ → ℝ := fun y => alphaF ν y + 2 * bfun ν y - 3 * ν y with hH
  have hH_ac : AbsolutelyContinuousOnInterval H x0 (1 / 2) :=
    (hA_ac.fun_add ((hP_ac.fun_add hQ_ac).const_mul 2)).fun_sub (hν_ac.const_mul 3)
  have hH_deriv : ∀ᵐ y, y ∈ uIcc x0 (1 / 2) → HasDerivAt H 0 y := by
    filter_upwards [hg.ae_hasDerivAt_integral, hP_int.ae_hasDerivAt_integral,
      hqq.ae_hasDerivAt_integral, h.ac.ae_differentiableAt] with y h1 h2 h3 h4 hy
    have hy' : y ∈ Icc x0 (1 / 2) := hI ▸ hy
    have hy0 : y ≠ 0 := (hx0.trans_le hy'.1).ne'
    have hy01 : y ∈ uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le zero_le_one]; exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
    have dG : HasDerivAt (fun y => ∫ t in y..(1 / 2), gInt ν t) (-gInt ν y) y := by
      have := (h1 hy (1 / 2) hhalf).neg
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.neg_apply]
      rw [intervalIntegral.integral_symm]
    have dA : HasDerivAt (alphaF ν)
        (((2:ℕ):ℝ) * y ^ (2 - 1) * (4 * alpha0 ν + ∫ t in y..(1 / 2), gInt ν t) +
          y ^ 2 * (0 + -gInt ν y)) y :=
      (hasDerivAt_pow 2 y).mul ((hasDerivAt_const y (4 * alpha0 ν)).add dG)
    have dP : HasDerivAt (fun y => ∫ a in y..(1 / 2), alpha ν a / a) (-(alpha ν y / y)) y := by
      have := (h2 hy (1 / 2) hhalf).neg
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.neg_apply]
      rw [intervalIntegral.integral_symm]
    have dQ : HasDerivAt (fun y => ∫ a in (1 / 2 : ℝ)..(y + 1 / 2), 3 * ν a / (1 - a))
        (qq ν y) y := by
      have := h3 (hsub hy) 0 left_mem_uIcc
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => Q_eq z)
    have dν : HasDerivAt ν (deriv ν y) y := (h4 hy01).hasDerivAt
    have dH := (dA.add ((dP.add dQ).const_mul 2)).sub (dν.const_mul 3)
    convert dH using 1
    · ext z; simp only [hH, Pi.add_apply, Pi.sub_apply, bfun]
    rw [alpha_of_mem ⟨hx0.trans_le hy'.1, hy'.2⟩]
    simp only [alphaF, gInt, qq]
    generalize ∫ t in y..(1 / 2), gInt ν t = G
    generalize ν (y + 1 / 2) / (1 / 2 - y) = V
    generalize deriv ν y = D
    field_simp
    ring_nf
  obtain ⟨C, hC⟩ := hH_ac.const_of_ae_hasDerivAt_zero hH_deriv
  have e1 := hC x0 left_mem_uIcc
  have e2 := hC (1 / 2) hhalf
  have hH0 : H (1 / 2) = 0 := by
    simp only [hH, alphaF_half, bfun_half, alpha0]; ring
  rw [alpha_of_mem ⟨hx0, hx1⟩]
  have : H x0 = 0 := by rw [e1, ← e2, hH0]
  simp only [hH] at this
  linarith

lemma bfun_nonneg (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1 / 2)) : 0 ≤ bfun ν x := by
  unfold bfun
  refine add_nonneg (intervalIntegral.integral_nonneg hx.2 fun a ha =>
    div_nonneg (alpha_nonneg h a) (by linarith [hx.1, ha.1]))
    (intervalIntegral.integral_nonneg (by linarith [hx.1]) fun a ha => ?_)
  have := h.nonneg a ⟨by linarith [ha.1], by linarith [ha.2, hx.2]⟩
  exact div_nonneg (by linarith) (by linarith [ha.2, hx.2])

lemma alpha_le (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : alpha ν x ≤ 3 * ν x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have := h.nonneg 0 hx; simp [alpha]; linarith
  rcases le_or_gt x (1 / 2) with hx1 | hx1
  · have e := key_identity h ⟨hx0, hx1⟩
    have := bfun_nonneg h ⟨hx0.le, hx1⟩
    linarith
  · rw [alpha_of_mem' ⟨hx1, hx.2⟩]

lemma nu_continuousAt (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : ContinuousAt ν x := by
  have := h.ac.continuousOn
  rw [uIcc_of_le zero_le_one] at this
  exact this.continuousAt (Icc_mem_nhds hx.1 hx.2)

lemma alpha_continuousAt (h : LevelHyp ν) {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1 / 2)
    (hx2 : x ≠ 1) : ContinuousAt (alpha ν) x := by
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [alpha, le_of_lt (show y < 0 from hy)]
  rcases lt_or_gt_of_ne hx1 with hx' | hx'
  · have hc := (alphaF_ac h (half_pos hx) (by linarith)).continuousOn
    rw [uIcc_of_le (by linarith)] at hc
    refine (hc.continuousAt (Icc_mem_nhds (by linarith) hx')).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx hx'] with y hy
    exact alpha_of_mem ⟨hy.1, hy.2.le⟩
  rcases lt_or_gt_of_ne hx2 with hx'' | hx''
  · refine ((nu_continuousAt h ⟨by linarith, hx''⟩).const_mul 3).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx' hx''] with y hy
    exact alpha_of_mem' ⟨hy.1, hy.2.le⟩
  · refine (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx''] with y hy
    have hy1 : 1 < y := hy
    unfold alpha; split_ifs <;> first | rfl | (exfalso; linarith)

lemma alpha_measurable (h : LevelHyp ν) : Measurable (alpha ν) := by
  refine measurable_of_countable_not_continuousAt ?_
  refine ((({0, 1 / 2, 1} : Set ℝ)).toFinite.countable).mono fun x hx => ?_
  by_contra hne
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
  exact hx (alpha_continuousAt h hne.1 hne.2.1 hne.2.2)

/-! ### The complete mix of the levels -/

/-- `δ(a) = min(a, 1 - a) / 2`. -/
def delta (a : ℝ) : ℝ := min a (1 - a) / 2

/-- `U[-1, 1]`; the variable `D` is `δ(A) V` with `V ∼ U[-1, 1]` independent of `A`. -/
def muV : Measure ℝ := unifI (-1) 1

lemma muV_apply (S : Set ℝ) : muV S = (ENNReal.ofReal 2)⁻¹ * volume (S ∩ Icc (-1) 1) := by
  simp only [muV, unifI, show (-1:ℝ) < 1 by norm_num, ↓reduceIte]
  rw [smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_Icc]
  norm_num

instance : IsProbabilityMeasure muV := unifI_isProb _ _

lemma delta_pos {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : 0 < delta a := by
  unfold delta; have := lt_min ha.1 (sub_pos.2 ha.2); linarith

lemma continuous_delta : Continuous delta :=
  (continuous_id.min (continuous_const.sub continuous_id)).div_const 2

lemma muV_preimage {a d : ℝ} (hd : 0 < d) (T : Set ℝ) :
    muV {v | a / 2 + d * v ∈ T} =
      ENNReal.ofReal (1 / (2 * d)) * volume (T ∩ Icc (a / 2 - d) (a / 2 + d)) := by
  rw [muV_apply]
  have e : {v | a / 2 + d * v ∈ T} ∩ Icc (-1) 1 =
      (fun v => d * v) ⁻¹' ((fun h => a / 2 + h) ⁻¹' (T ∩ Icc (a / 2 - d) (a / 2 + d))) := by
    ext v
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨hv, h1, h2⟩
      exact ⟨hv, by nlinarith, by nlinarith⟩
    · rintro ⟨hv, h1, h2⟩
      refine ⟨hv, ?_, ?_⟩
      · by_contra! hc; nlinarith
      · by_contra! hc; nlinarith
  rw [e, Real.volume_preimage_mul_left hd.ne', measure_preimage_add, ← mul_assoc,
    abs_of_pos (inv_pos.2 hd), ← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 2
  field_simp

lemma delta_of_le {a : ℝ} (ha : a ≤ 1 / 2) : delta a = a / 2 := by
  unfold delta; rw [min_eq_left (by linarith)]

lemma delta_of_ge {a : ℝ} (ha : 1 / 2 ≤ a) : delta a = (1 - a) / 2 := by
  unfold delta; rw [min_eq_right (by linarith)]

lemma alphaDiv_intervalIntegrable (h : LevelHyp ν) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    IntervalIntegrable (fun a => alpha ν a / a) volume x (1 / 2) := by
  have hI : uIcc x (1 / 2) = Icc x (1 / 2) := uIcc_of_le hx1
  refine ContinuousOn.intervalIntegrable ?_
  refine ((alphaF_ac h hx0 hx1).continuousOn.div continuousOn_id fun a ha => ?_).congr
    fun a ha => ?_
  · rw [hI] at ha; simp only [id]; linarith [ha.1]
  · rw [hI] at ha
    simp only [alpha_of_mem ⟨hx0.trans_le ha.1, ha.2⟩, Pi.div_apply, id]

/-- The distribution of the largest level `A`, with density `α`. -/
def muA (ν : ℝ → ℝ) : Measure ℝ := volume.withDensity fun a => ENNReal.ofReal (alpha ν a)

/-- `B = A/2 + D` with `D = δ(A) V`. -/
def Bv (p : ℝ × ℝ) : ℝ := p.1 / 2 + delta p.1 * p.2

/-- `C = A/2 - D` with `D = δ(A) V`. -/
def Cv (p : ℝ × ℝ) : ℝ := p.1 / 2 - delta p.1 * p.2

/-- The joint distribution of `(A, V)`. -/
def P0 (ν : ℝ → ℝ) : Measure (ℝ × ℝ) := (muA ν).prod muV

lemma continuous_Bv : Continuous Bv :=
  (continuous_fst.div_const 2).add ((continuous_delta.comp continuous_fst).mul continuous_snd)

lemma continuous_Cv : Continuous Cv :=
  (continuous_fst.div_const 2).sub ((continuous_delta.comp continuous_fst).mul continuous_snd)

/-- The density `b` of `B` and `C`, extended by `0` outside `[0, 1/2]`. -/
def bI (ν : ℝ → ℝ) (x : ℝ) : ℝ := (Icc (0:ℝ) (1 / 2)).indicator (bfun ν) x

/-- The weight `α(a) / (2 δ(a))` of the uniform distribution on `[a/2 - δ(a), a/2 + δ(a)]`. -/
def phi (ν : ℝ → ℝ) (a : ℝ) : ENNReal := ENNReal.ofReal (alpha ν a / (2 * delta a))

/-- The set `{(a, x) : 0 < a < 1, x ∈ T, |x - a/2| ≤ δ(a)}`. -/
def Eset (T : Set ℝ) : Set (ℝ × ℝ) :=
  Prod.fst ⁻¹' Ioo 0 1 ∩ Prod.snd ⁻¹' T ∩ {p | p.1 / 2 - delta p.1 ≤ p.2} ∩
    {p | p.2 ≤ p.1 / 2 + delta p.1}

lemma measurableSet_Eset {T : Set ℝ} (hT : MeasurableSet T) : MeasurableSet (Eset T) := by
  have c1 : Continuous fun p : ℝ × ℝ => p.1 / 2 - delta p.1 :=
    (continuous_fst.div_const 2).sub (continuous_delta.comp continuous_fst)
  have c2 : Continuous fun p : ℝ × ℝ => p.1 / 2 + delta p.1 :=
    (continuous_fst.div_const 2).add (continuous_delta.comp continuous_fst)
  exact (((measurable_fst measurableSet_Ioo).inter (measurable_snd hT)).inter
    (measurableSet_le c1.measurable measurable_snd)).inter
    (measurableSet_le measurable_snd c2.measurable)

lemma mem_Eset {T : Set ℝ} {a x : ℝ} : (a, x) ∈ Eset T ↔
    a ∈ Ioo 0 1 ∧ x ∈ T ∧ a / 2 - delta a ≤ x ∧ x ≤ a / 2 + delta a := by
  simp only [Eset, mem_inter_iff, mem_preimage, mem_ofPred_eq, and_assoc]

lemma phi_measurable (h : LevelHyp ν) : Measurable (phi ν) :=
  ((alpha_measurable h).div (continuous_delta.measurable.const_mul 2)).ennreal_ofReal

lemma inner_a (h : LevelHyp ν) {a : ℝ} (ha : a ≠ 1) {T : Set ℝ} (hT : MeasurableSet T) :
    ENNReal.ofReal (alpha ν a) * muV (Prod.mk a ⁻¹' (Bv ⁻¹' T)) =
      ∫⁻ x, (Eset T).indicator (fun p => phi ν p.1) (a, x) := by
  by_cases haI : a ∈ Ioo (0:ℝ) 1
  · have hd := delta_pos haI
    have e : (fun x => (Eset T).indicator (fun p => phi ν p.1) (a, x)) =
        (T ∩ Icc (a / 2 - delta a) (a / 2 + delta a)).indicator fun _ => phi ν a := by
      ext x
      by_cases hx : (a, x) ∈ Eset T
      · have hx' := mem_Eset.1 hx
        have hx'' : x ∈ T ∩ Icc (a / 2 - delta a) (a / 2 + delta a) := ⟨hx'.2.1, hx'.2.2⟩
        rw [indicator_of_mem hx, indicator_of_mem hx'']
      · have hx' : x ∉ T ∩ Icc (a / 2 - delta a) (a / 2 + delta a) := fun hh =>
          hx (mem_Eset.2 ⟨haI, hh.1, hh.2.1, hh.2.2⟩)
        rw [indicator_of_notMem hx, indicator_of_notMem hx']
    rw [e, lintegral_indicator_const (hT.inter measurableSet_Icc)]
    have e2 : Prod.mk a ⁻¹' (Bv ⁻¹' T) = {v | a / 2 + delta a * v ∈ T} := rfl
    rw [e2, muV_preimage hd, ← mul_assoc, phi, ← ENNReal.ofReal_mul (alpha_nonneg h a),
      div_eq_mul_one_div (alpha ν a)]
  · have h0 : alpha ν a = 0 := by
      simp only [mem_Ioo, not_and_or, not_lt] at haI
      unfold alpha
      split_ifs <;> first | rfl | (exfalso; rcases haI with h1 | h1 <;>
        first | linarith | exact ha (le_antisymm ‹_› h1))
    have e : (fun x => (Eset T).indicator (fun p => phi ν p.1) (a, x)) = fun _ => 0 := by
      ext x
      exact indicator_of_notMem (fun hh => haI (mem_Eset.1 hh).1) _
    rw [e, h0]; simp

lemma Eset_slice {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) {a : ℝ} :
    (a ∈ Ioo (0:ℝ) 1 ∧ a / 2 - delta a ≤ x ∧ x ≤ a / 2 + delta a) ↔
      a ∈ Icc x (1 / 2) ∪ Ioc (1 / 2) (x + 1 / 2) := by
  constructor
  · rintro ⟨⟨a0, a1⟩, l, r⟩
    rcases le_or_gt a (1 / 2) with ha | ha
    · rw [delta_of_le ha] at l r; left; exact ⟨by linarith, ha⟩
    · rw [delta_of_ge ha.le] at l r; right; exact ⟨ha, by linarith⟩
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · rw [delta_of_le r]; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rw [delta_of_ge l.le]; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma Eset_empty {x : ℝ} (hx : x < 0 ∨ 1 / 2 < x) {a : ℝ} :
    ¬ (a ∈ Ioo (0:ℝ) 1 ∧ a / 2 - delta a ≤ x ∧ x ≤ a / 2 + delta a) := by
  rintro ⟨_, l, r⟩
  have h1 : delta a ≤ a / 2 := by unfold delta; linarith [min_le_left a (1 - a)]
  have h2 : delta a ≤ (1 - a) / 2 := by unfold delta; linarith [min_le_right a (1 - a)]
  rcases hx with hx | hx <;> linarith

lemma P_nonneg (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1 / 2)) :
    0 ≤ ∫ a in x..(1 / 2), alpha ν a / a :=
  intervalIntegral.integral_nonneg hx.2 fun a ha =>
    div_nonneg (alpha_nonneg h a) (by linarith [hx.1, ha.1])

lemma Q_nonneg (h : LevelHyp ν) {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1 / 2)) :
    0 ≤ ∫ a in (1 / 2 : ℝ)..(x + 1 / 2), 3 * ν a / (1 - a) := by
  refine intervalIntegral.integral_nonneg (by linarith [hx.1]) fun a ha => ?_
  have := h.nonneg a ⟨by linarith [ha.1], by linarith [ha.2, hx.2]⟩
  exact div_nonneg (by linarith) (by linarith [ha.2, hx.2])

lemma inner_x (h : LevelHyp ν) {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1 / 2) (T : Set ℝ) :
    ∫⁻ a, (Eset T).indicator (fun p => phi ν p.1) (a, x) =
      T.indicator (fun x => ENNReal.ofReal (bI ν x)) x := by
  by_cases hxT : x ∉ T
  · rw [indicator_of_notMem hxT]
    have e : (fun a => (Eset T).indicator (fun p => phi ν p.1) (a, x)) = fun _ => 0 := by
      ext a; exact indicator_of_notMem (fun hh => hxT (mem_Eset.1 hh).2.1) _
    rw [e, lintegral_zero]
  push Not at hxT
  rw [indicator_of_mem hxT]
  by_cases hxI : x < 0 ∨ 1 / 2 < x
  · have e : (fun a => (Eset T).indicator (fun p => phi ν p.1) (a, x)) = fun _ => 0 := by
      ext a
      exact indicator_of_notMem (fun hh => Eset_empty hxI
        ⟨(mem_Eset.1 hh).1, (mem_Eset.1 hh).2.2⟩) _
    have hb : bI ν x = 0 := indicator_of_notMem (fun hh => by
      rcases hxI with hh' | hh' <;> linarith [hh.1, hh.2]) _
    rw [e, lintegral_zero, hb, ENNReal.ofReal_zero]
  push Not at hxI
  have hxp : 0 < x := lt_of_le_of_ne hxI.1 (Ne.symm hx0)
  have hxq : x < 1 / 2 := lt_of_le_of_ne hxI.2 hx1
  set S := Icc x (1 / 2) ∪ Ioc (1 / 2) (x + 1 / 2) with hS
  have e : (fun a => (Eset T).indicator (fun p => phi ν p.1) (a, x)) = S.indicator (phi ν) := by
    ext a
    by_cases ha : a ∈ S
    · obtain ⟨h1, h2, h3⟩ := (Eset_slice hxp hxq).2 ha
      rw [indicator_of_mem ha, indicator_of_mem (mem_Eset.2 ⟨h1, hxT, h2, h3⟩)]
    · rw [indicator_of_notMem ha, indicator_of_notMem fun hh => ha ((Eset_slice hxp hxq).1
        ⟨(mem_Eset.1 hh).1, (mem_Eset.1 hh).2.2⟩)]
  have hdisj : Disjoint (Icc x (1 / 2)) (Ioc (1 / 2) (x + 1 / 2)) :=
    Set.disjoint_left.2 fun a h1 h2 => by linarith [h1.2, h2.1]
  rw [e, lintegral_indicator (measurableSet_Icc.union measurableSet_Ioc),
    lintegral_union measurableSet_Ioc hdisj]
  have hxI' : x ∈ Icc (0:ℝ) (1 / 2) := ⟨hxp.le, hxq.le⟩
  have I1 : ∫⁻ a in Icc x (1 / 2), phi ν a = ENNReal.ofReal (∫ a in x..(1 / 2), alpha ν a / a) := by
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun a => ENNReal.ofReal (alpha ν a / a))
      fun a ha => by rw [phi, delta_of_le ha.2, show 2 * (a / 2) = a by ring]]
    rw [intervalIntegral.integral_of_le hxq.le, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxq.le).1
        (alphaDiv_intervalIntegrable h hxp hxq.le)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact div_nonneg (alpha_nonneg h a) (by linarith [ha.1])
  have I2 : ∫⁻ a in Ioc (1 / 2) (x + 1 / 2), phi ν a =
      ENNReal.ofReal (∫ a in (1 / 2 : ℝ)..(x + 1 / 2), 3 * ν a / (1 - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun a => ENNReal.ofReal (3 * ν a / (1 - a))) fun a ha => by
        rw [phi, delta_of_ge ha.1.le, alpha_of_mem' ⟨ha.1, by linarith [ha.2]⟩,
          show 2 * ((1 - a) / 2) = 1 - a by ring]]
    rw [intervalIntegral.integral_of_le (by linarith), ofReal_integral_eq_lintegral_ofReal]
    · have hsub : Ioc (1 / 2 : ℝ) (x + 1 / 2) ⊆ Icc (1 / 2) 1 :=
        Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (show x + 1 / 2 ≤ 1 by linarith))
      have := (h.fin.mono_set hsub).const_mul 3
      refine this.congr ?_
      filter_upwards with a
      simp only [mul_div_assoc]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have := h.nonneg a ⟨by linarith [ha.1], by linarith [ha.2]⟩
      exact div_nonneg (by linarith) (by linarith [ha.2])
  rw [I1, I2, bI, indicator_of_mem hxI', bfun,
    ENNReal.ofReal_add (P_nonneg h hxI') (Q_nonneg h hxI')]

instance : SFinite (muA ν) := by unfold muA; infer_instance

/-- The distribution of `B` has the density `b` on `[0, 1/2]` (Fubini). -/
theorem lawB (h : LevelHyp ν) {T : Set ℝ} (hT : MeasurableSet T) :
    P0 ν (Bv ⁻¹' T) = ∫⁻ x in T, ENNReal.ofReal (bI ν x) := by
  have hS : MeasurableSet (Bv ⁻¹' T) := continuous_Bv.measurable hT
  have hmA : Measurable fun a => ENNReal.ofReal (alpha ν a) :=
    (alpha_measurable h).ennreal_ofReal
  rw [P0, Measure.prod_apply hS, muA,
    lintegral_withDensity_eq_lintegral_mul _ hmA (measurable_measure_prodMk_left hS)]
  have ha1 : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1 := by simp [ae_iff, measure_singleton]
  have hx0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 / 2 := by simp [ae_iff, measure_singleton]
  calc ∫⁻ a, ((fun a => ENNReal.ofReal (alpha ν a)) *
        fun a => muV (Prod.mk a ⁻¹' (Bv ⁻¹' T))) a
      = ∫⁻ a, ∫⁻ x, (Eset T).indicator (fun p => phi ν p.1) (a, x) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ha1] with a ha
        exact inner_a h ha hT
    _ = ∫⁻ x, ∫⁻ a, (Eset T).indicator (fun p => phi ν p.1) (a, x) := by
        refine lintegral_lintegral_swap ?_
        exact (((phi_measurable h).comp measurable_fst).indicator
          (measurableSet_Eset hT)).aemeasurable
    _ = ∫⁻ x, T.indicator (fun x => ENNReal.ofReal (bI ν x)) x := by
        refine lintegral_congr_ae ?_
        filter_upwards [hx0, hx1] with x h0 h1
        exact inner_x h h0 h1 T
    _ = ∫⁻ x in T, ENNReal.ofReal (bI ν x) := lintegral_indicator hT _

lemma muV_map_neg : muV.map Neg.neg = muV := by
  ext S hS
  rw [Measure.map_apply measurable_neg hS, muV_apply, muV_apply]
  congr 1
  have : Neg.neg ⁻¹' S ∩ Icc (-1:ℝ) 1 = Neg.neg ⁻¹' (S ∩ Icc (-1) 1) := by
    ext v; simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, by linarith, by linarith⟩
  rw [this]; exact Measure.measure_preimage_neg volume _

/-- `C` has the same distribution as `B`, because `V` is symmetric. -/
theorem lawC (T : Set ℝ) (hT : MeasurableSet T) : P0 ν (Cv ⁻¹' T) = P0 ν (Bv ⁻¹' T) := by
  have hm : Measurable (Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
    measurable_id.prodMap measurable_neg
  have hP : (P0 ν).map (Prod.map id Neg.neg) = P0 ν := by
    rw [P0, ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id,
      muV_map_neg]
  have e : Cv ⁻¹' T = Prod.map id Neg.neg ⁻¹' (Bv ⁻¹' T) := by
    ext p; simp [Cv, Bv, sub_eq_add_neg]
  rw [e, ← Measure.map_apply hm (continuous_Bv.measurable hT), hP]

/-- The distribution with density `ν` on `[0, 1]`. -/
def nuMeas (ν : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal ((Icc (0:ℝ) 1).indicator ν x)

/-- The symmetric distribution on `[-1, 1]` whose absolute value has the density `ν`: the
average of `nuMeas ν` and its reflection. -/
def symNu (ν : ℝ → ℝ) : Measure ℝ := (2 : ENNReal)⁻¹ • (nuMeas ν + (nuMeas ν).map Neg.neg)

lemma ennreal_comb {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (e : a + 2 * b = 3 * c) :
    ENNReal.ofReal a + 2 * ENNReal.ofReal b = 3 * ENNReal.ofReal c := by
  have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
  have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := by simp
  rw [h2, h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add ha (by positivity), e]

lemma dens_ae (h : LevelHyp ν) : ∀ᵐ x ∂(volume : Measure ℝ),
    ENNReal.ofReal (alpha ν x) + 2 * ENNReal.ofReal (bI ν x) =
      3 * ENNReal.ofReal ((Icc (0:ℝ) 1).indicator ν x) := by
  have hx0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [hx0] with x hx
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h1 : alpha ν x = 0 := by simp [alpha, hx.le]
    have h2 : bI ν x = 0 := indicator_of_notMem (fun hh => by linarith [hh.1]) _
    have h3 : (Icc (0:ℝ) 1).indicator ν x = 0 :=
      indicator_of_notMem (fun hh => by linarith [hh.1]) _
    simp [h1, h2, h3]
  rcases le_or_gt x (1 / 2) with hx1 | hx1
  · have h2 : bI ν x = bfun ν x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) (1 / 2) from ⟨hx.le, hx1⟩) _
    have h3 : (Icc (0:ℝ) 1).indicator ν x = ν x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨hx.le, by linarith⟩) _
    rw [h2, h3]
    exact ennreal_comb (alpha_nonneg h x) (bfun_nonneg h ⟨hx.le, hx1⟩) (key_identity h ⟨hx, hx1⟩)
  have h2 : bI ν x = 0 := indicator_of_notMem (fun hh => by linarith [hh.2]) _
  rcases le_or_gt x 1 with hx2 | hx2
  · have h3 : (Icc (0:ℝ) 1).indicator ν x = ν x :=
      indicator_of_mem (show x ∈ Icc (0:ℝ) 1 from ⟨hx.le, hx2⟩) _
    rw [h2, h3, alpha_of_mem' ⟨hx1, hx2⟩]
    exact ennreal_comb (by linarith [h.nonneg x ⟨hx.le, hx2⟩]) le_rfl (by ring)
  · have h1 : alpha ν x = 0 := by
      unfold alpha; split_ifs <;> first | rfl | (exfalso; linarith)
    have h3 : (Icc (0:ℝ) 1).indicator ν x = 0 :=
      indicator_of_notMem (fun hh => by linarith [hh.2]) _
    simp [h1, h2, h3]

/-- `α + 2 b = 3 ν` as distributions: `P(A ∈ T) + 2 P(B ∈ T) = 3 ∫_T ν`. -/
theorem sumAB (h : LevelHyp ν) {T : Set ℝ} (hT : MeasurableSet T) :
    muA ν T + 2 * P0 ν (Bv ⁻¹' T) = 3 * nuMeas ν T := by
  rw [lawB h hT, muA, nuMeas, withDensity_apply _ hT, withDensity_apply _ hT,
    ← lintegral_const_mul' _ _ (by simp),
    ← lintegral_add_left (alpha_measurable h).ennreal_ofReal,
    ← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_congr_ae (ae_restrict_of_ae (dens_ae h))

lemma P0_fst (T : Set ℝ) : P0 ν (Prod.fst ⁻¹' T) = muA ν T := by
  rw [← prod_univ, P0, Measure.prod_prod, measure_univ, mul_one]

lemma nuMeas_univ (h : LevelHyp ν) : nuMeas ν univ = 1 := by
  rw [nuMeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have e : (fun x => ENNReal.ofReal ((Icc (0:ℝ) 1).indicator ν x)) =
      (Icc (0:ℝ) 1).indicator fun x => ENNReal.ofReal (ν x) := by
    ext x; by_cases hx : x ∈ Icc (0:ℝ) 1 <;> simp [hx]
  have hc := h.ac.continuousOn
  rw [uIcc_of_le zero_le_one] at hc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] ν := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact h.nonneg x hx
  rw [e, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc hnn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, h.int_one,
    ENNReal.ofReal_one]

lemma muA_univ (h : LevelHyp ν) : muA ν univ = 1 := by
  have e := sumAB h MeasurableSet.univ
  rw [preimage_univ, ← P0_fst univ, preimage_univ, nuMeas_univ h, mul_one] at e
  have hfin : P0 ν univ ≠ ⊤ := by
    intro htop; rw [htop] at e; simp at e
  have : 3 * P0 ν univ = 3 * 1 := by
    rw [mul_one]
    calc 3 * P0 ν univ = P0 ν univ + 2 * P0 ν univ := by ring
      _ = 3 := e
  have := (ENNReal.mul_right_inj (by norm_num) (by simp)).1 this
  rw [← P0_fst univ, preimage_univ, this]

/-- **Lemma 69**: `α` is a probability density on `[0, 1]`. -/
theorem alpha_integral (h : LevelHyp ν) : ∫ x in (0:ℝ)..1, alpha ν x = 1 := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (alpha_nonneg h))
      (alpha_measurable h).aestronglyMeasurable]
  · have := muA_univ h
    rw [muA, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    rw [this, ENNReal.toReal_one]
  · simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    unfold alpha
    split_ifs <;> first | rfl | (exfalso; rcases hx with hx | hx <;> linarith)

/-- A random sign. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The vector `(A, -B, -C)`. -/
def W (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, -Bv p, -Cv p]

lemma measurable_W (j : Fin 3) : Measurable fun p => W p j := by
  fin_cases j
  · exact measurable_fst
  · exact continuous_Bv.measurable.neg
  · exact continuous_Cv.measurable.neg

/-- The map `(A, V) ↦ (ε W_{π(1)}, ε W_{π(2)}, ε W_{π(3)})` for a sign `ε` and a permutation `π`. -/
def zmap (b : Bool) (σ : Equiv.Perm (Fin 3)) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  fun i => sgn b * W p (σ i)

lemma measurable_zmap (b : Bool) (σ : Equiv.Perm (Fin 3)) : Measurable (zmap b σ) :=
  Measurable.of_eval fun i => measurable_const.mul (measurable_W (σ i))

/-- The complete mix `(Z₁, Z₂, Z₃)` of **Lemma 69**: the average over the random sign `ε` and the
uniformly random permutation `π` of the images of the law of `(A, V)`. -/
def levelMix (ν : ℝ → ℝ) : Measure (Fin 3 → ℝ) :=
  (12 : ENNReal)⁻¹ • ∑ b : Bool, ∑ σ : Equiv.Perm (Fin 3), (P0 ν).map (zmap b σ)

lemma card_perm_fiber : ∀ i j : Fin 3,
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ i = j).card = 2 := by decide

lemma perm_sum (f : Fin 3 → ENNReal) (i : Fin 3) :
    ∑ σ : Equiv.Perm (Fin 3), f (σ i) = 2 * ∑ j, f j := by
  calc ∑ σ : Equiv.Perm (Fin 3), f (σ i)
      = ∑ j, ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => σ i = j), f (σ i) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ j, ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => σ i = j), f j := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ hσ => ?_
        rw [(Finset.mem_filter.1 hσ).2]
    _ = ∑ j, 2 * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, card_perm_fiber, nsmul_eq_mul]; norm_num
    _ = 2 * ∑ j, f j := Finset.mul_sum _ _ _ |>.symm

lemma levelMix_apply {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S) :
    levelMix ν S = (12 : ENNReal)⁻¹ *
      ∑ b : Bool, ∑ σ : Equiv.Perm (Fin 3), P0 ν (zmap b σ ⁻¹' S) := by
  simp only [levelMix, smul_apply, FunLike.coe_sum, Finset.sum_apply, smul_eq_mul]
  simp only [Measure.map_apply (measurable_zmap _ _) hS]

lemma P0_sgn_W (b : Bool) {T : Set ℝ} (hT : MeasurableSet T) :
    ∑ j, P0 ν ((fun p => sgn b * W p j) ⁻¹' T) =
      muA ν ((fun x => sgn b * x) ⁻¹' T) + 2 * P0 ν (Bv ⁻¹' ((fun x => -(sgn b * x)) ⁻¹' T)) := by
  have hT' : MeasurableSet ((fun x => -(sgn b * x)) ⁻¹' T) :=
    (measurable_const.mul measurable_id).neg hT
  rw [Fin.sum_univ_three, two_mul, ← add_assoc]
  congr 1
  · congr 1
    · rw [← P0_fst]; rfl
    · congr 1; ext p; simp [W, mul_neg]
  · rw [← lawC _ hT']; congr 1; ext p; simp [W, mul_neg]

lemma sgn_preimage_true (T : Set ℝ) : (fun x => sgn true * x) ⁻¹' T = T := by
  ext; simp [sgn]

lemma sgn_preimage_false (T : Set ℝ) : (fun x => sgn false * x) ⁻¹' T = Neg.neg ⁻¹' T := by
  ext; simp [sgn]

lemma sgn_neg_preimage_true (T : Set ℝ) : (fun x => -(sgn true * x)) ⁻¹' T = Neg.neg ⁻¹' T := by
  ext; simp [sgn]

lemma sgn_neg_preimage_false (T : Set ℝ) : (fun x => -(sgn false * x)) ⁻¹' T = T := by
  ext; simp [sgn]

/-- Each coordinate of `levelMix ν` has the distribution `symNu ν`. -/
theorem levelMix_marginal (h : LevelHyp ν) (i : Fin 3) :
    (levelMix ν).map (fun z => z i) = symNu ν := by
  ext T hT
  rw [Measure.map_apply (measurable_pi_apply i) hT, levelMix_apply (measurable_pi_apply i hT)]
  have e1 : ∀ b, ∑ σ : Equiv.Perm (Fin 3), P0 ν (zmap b σ ⁻¹' ((fun z => z i) ⁻¹' T)) =
      2 * (muA ν ((fun x => sgn b * x) ⁻¹' T) +
        2 * P0 ν (Bv ⁻¹' ((fun x => -(sgn b * x)) ⁻¹' T))) := fun b => by
    rw [← P0_sgn_W b hT]
    exact perm_sum (fun j => P0 ν ((fun p => sgn b * W p j) ⁻¹' T)) i
  rw [Fintype.sum_bool, e1, e1, sgn_preimage_true, sgn_preimage_false, sgn_neg_preimage_true,
    sgn_neg_preimage_false]
  have hTn : MeasurableSet (Neg.neg ⁻¹' T) := measurable_neg hT
  have k : muA ν T + 2 * P0 ν (Bv ⁻¹' (Neg.neg ⁻¹' T)) +
      (muA ν (Neg.neg ⁻¹' T) + 2 * P0 ν (Bv ⁻¹' T)) =
      3 * (nuMeas ν T + nuMeas ν (Neg.neg ⁻¹' T)) := by
    rw [mul_add, ← sumAB h hT, ← sumAB h hTn]; ring
  rw [← mul_add, k, symNu, smul_apply, add_apply,
    Measure.map_apply measurable_neg hT, smul_eq_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (12 : ENNReal) = 2 * 6 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    mul_assoc, mul_assoc, show (2 : ENNReal) * 3 = 6 by norm_num,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

lemma P0_ae :
    ∀ᵐ p ∂(P0 ν), p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ Icc (-1:ℝ) 1 := by
  rw [ae_iff]
  refine measure_mono_null (t := Prod.fst ⁻¹' (Icc (0:ℝ) 1)ᶜ ∪ Prod.snd ⁻¹' (Icc (-1:ℝ) 1)ᶜ)
    (fun p hp => ?_) (measure_union_null ?_ ?_)
  · simp only [mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  · rw [P0_fst, muA, withDensity_apply _ measurableSet_Icc.compl]
    refine (setLIntegral_congr_fun measurableSet_Icc.compl (g := fun _ => 0) fun x hx => ?_).trans
      lintegral_zero
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    have : alpha ν x = 0 := by
      unfold alpha; split_ifs <;> first | rfl | (exfalso; rcases hx with hx | hx <;> linarith)
    simp [this]
  · rw [← univ_prod, P0, Measure.prod_prod, muV_apply, compl_inter_self, measure_empty,
      mul_zero, mul_zero]

lemma levelMix_ae {Pr : (Fin 3 → ℝ) → Prop} (hP : MeasurableSet {z | Pr z})
    (hall : ∀ b σ (p : ℝ × ℝ), p.1 ∈ Icc (0:ℝ) 1 → p.2 ∈ Icc (-1:ℝ) 1 → Pr (zmap b σ p)) :
    ∀ᵐ z ∂(levelMix ν), Pr z := by
  rw [ae_iff]
  change levelMix ν {z | Pr z}ᶜ = 0
  rw [levelMix_apply hP.compl]
  have : ∀ b σ, P0 ν (zmap b σ ⁻¹' {z | Pr z}ᶜ) = 0 := fun b σ => by
    have := P0_ae (ν := ν)
    have h2 : ∀ᵐ p ∂(P0 ν), Pr (zmap b σ p) := by
      filter_upwards [this] with p hp using hall b σ p hp.1 hp.2
    exact ae_iff.1 h2
  simp only [this, Finset.sum_const_zero, mul_zero]

lemma zmap_sum (b : Bool) (σ : Equiv.Perm (Fin 3)) (p : ℝ × ℝ) : ∑ i, zmap b σ p i = 0 := by
  simp only [zmap]
  rw [← Finset.mul_sum, Equiv.sum_comp σ (fun j => W p j), Fin.sum_univ_three]
  simp only [W, Bv, Cv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one]
  ring_nf

lemma abs_B_le {p : ℝ × ℝ} (h1 : p.1 ∈ Icc (0:ℝ) 1) (h2 : p.2 ∈ Icc (-1:ℝ) 1) :
    |Bv p| ≤ 1 / 2 ∧ |Cv p| ≤ 1 / 2 := by
  have d0 : 0 ≤ delta p.1 := by unfold delta; have := le_min h1.1 (sub_nonneg.2 h1.2); linarith
  have d1 : delta p.1 ≤ p.1 / 2 := by unfold delta; linarith [min_le_left p.1 (1 - p.1)]
  have d2 : delta p.1 ≤ (1 - p.1) / 2 := by unfold delta; linarith [min_le_right p.1 (1 - p.1)]
  have u1 : delta p.1 * p.2 ≤ delta p.1 := by nlinarith [h2.2]
  have u2 : -delta p.1 ≤ delta p.1 * p.2 := by nlinarith [h2.1]
  simp only [Bv, Cv]
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- **Lemma 69** (`o:lem:levels`). Under the hypotheses `LevelHyp ν`: `α ≥ 0` and `∫₀¹ α = 1`, so
`α` is a probability density on `[0, 1]`; the law `levelMix ν` of `(Z₁, Z₂, Z₃)`, built from `A`
with density `α`, `D` uniform on `[-δ(A), δ(A)]` (as `δ(A) V` with `V ∼ U[-1, 1]`), `B = A/2 + D`,
`C = A/2 - D`, a random sign and a uniformly random permutation, is a `3`-complete mix of the
symmetric distribution `symNu ν` on `[-1, 1]` whose absolute value has the density `ν`; almost
surely `Z₁ + Z₂ + Z₃ = 0` and at least two of `|Z₁|, |Z₂|, |Z₃|` are at most `1/2`. -/
theorem levels (h : LevelHyp ν) :
    (∀ x, 0 ≤ alpha ν x) ∧ (∫ x in (0:ℝ)..1, alpha ν x = 1) ∧
      IsCompleteMix 3 (symNu ν) (levelMix ν) ∧
      (∀ᵐ z ∂(levelMix ν), ∑ i, z i = 0) ∧
      (∀ᵐ z ∂(levelMix ν), ∃ i j : Fin 3, i ≠ j ∧ |z i| ≤ 1 / 2 ∧ |z j| ≤ 1 / 2) := by
  have hsum : ∀ᵐ z ∂(levelMix ν), ∑ i, z i = 0 :=
    levelMix_ae (ν := ν) (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
      measurable_pi_apply i) measurable_const) fun b σ p _ _ => zmap_sum b σ p
  have hprob : IsProbabilityMeasure (levelMix ν) := by
    constructor
    have := congrArg (fun m : Measure ℝ => m univ) (levelMix_marginal h 0)
    rw [Measure.map_apply (measurable_pi_apply 0) MeasurableSet.univ, preimage_univ] at this
    rw [this, symNu, smul_apply, add_apply, Measure.map_apply measurable_neg MeasurableSet.univ,
      preimage_univ, nuMeas_univ h, smul_eq_mul, one_add_one_eq_two,
      ENNReal.inv_mul_cancel (by simp) (by simp)]
  refine ⟨alpha_nonneg h, alpha_integral h, ⟨hprob, ⟨0, hsum⟩, levelMix_marginal h⟩, hsum, ?_⟩
  refine levelMix_ae (ν := ν) ?_ fun b σ p h1 h2 => ?_
  · simp only [ofPred_exists]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
    simp only [ofPred_and]
    exact (MeasurableSet.const _).inter ((measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply j))
        measurable_const))
  · obtain ⟨hB, hC⟩ := abs_B_le h1 h2
    refine ⟨σ.symm 1, σ.symm 2, fun e => absurd (σ.symm.injective e) (by decide), ?_, ?_⟩
    · simp only [zmap, Equiv.apply_symm_apply, abs_mul, abs_sgn, one_mul]
      simpa [W] using hB
    · simp only [zmap, Equiv.apply_symm_apply, abs_mul, abs_sgn, one_mul]
      simpa [W] using hC

end Levels

/-! ## Proposition 71(c) -/

section Reduce

variable {d : ℕ}

/-- The homothety `x ↦ c + r (x - c)`. -/
def homo (c : Fin d → ℝ) (r : ℝ) (x : Fin d → ℝ) : Fin d → ℝ := c + r • (x - c)

lemma homo_eq (c : Fin d → ℝ) (r : ℝ) : homo c r = ⇑(AffineMap.homothety c r) := by
  ext1 x; simp [homo, AffineMap.homothety_apply, add_comm]

lemma continuous_homo (c : Fin d → ℝ) (r : ℝ) : Continuous (homo c r) := by
  unfold homo; fun_prop

lemma homo_comp (c : Fin d → ℝ) (r s : ℝ) : homo c r ∘ homo c s = homo c (r * s) := by
  ext1 x; simp only [Function.comp, homo, add_sub_cancel_left, smul_smul]

lemma homo_one (c : Fin d → ℝ) : homo c 1 = id := by
  ext1 x; simp [homo]

lemma volume_homo_image (c : Fin d → ℝ) (r : ℝ) (A : Set (Fin d → ℝ)) :
    volume (homo c r '' A) = ENNReal.ofReal |r ^ d| * volume A := by
  rw [homo_eq, Measure.addHaar_image_homothety, Module.finrank_fin_fun]

/-- The image of a uniform distribution under a homothety with ratio `r ≠ 0` is the uniform
distribution on the image. -/
theorem map_unifSet_homo (c : Fin d → ℝ) {r : ℝ} (hr : r ≠ 0) (K : Set (Fin d → ℝ)) :
    (unifSet K).map (homo c r) = unifSet (homo c r '' K) := by
  have ha0 : ENNReal.ofReal |r ^ d| ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact pow_ne_zero _ hr
  have hat : ENNReal.ofReal |r ^ d| ≠ ⊤ := ENNReal.ofReal_ne_top
  ext S hS
  have hm := (continuous_homo c r).measurable
  rw [Measure.map_apply hm hS, unifSet, unifSet, smul_apply, smul_apply,
    Measure.restrict_apply (hm hS), Measure.restrict_apply hS, smul_eq_mul, smul_eq_mul,
    volume_homo_image]
  have e : S ∩ homo c r '' K = homo c r '' (K ∩ homo c r ⁻¹' S) := by
    rw [image_inter_preimage, inter_comm]
  rw [e, volume_homo_image, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat), mul_comm (volume K)⁻¹,
    mul_assoc, ← mul_assoc (volume K)⁻¹, mul_comm (volume K)⁻¹, mul_assoc, ← mul_assoc,
    ENNReal.inv_mul_cancel ha0 hat, one_mul, mul_comm, inter_comm]

lemma unifSet_integrable {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hK0 : volume K ≠ 0) :
    Integrable id (unifSet K) := by
  unfold unifSet
  exact Integrable.smul_measure (continuousOn_id.integrableOn_compact hK)
    (ENNReal.inv_ne_top.2 hK0)

lemma mean_eq_homo {c x : Fin d → ℝ} (hd : (d:ℝ) ≠ 0) :
    (d:ℝ)⁻¹ • (((d:ℝ) + 1) • c - x) = homo c (-(d:ℝ)⁻¹) x := by
  have hdd : (d:ℝ)⁻¹ * ((d:ℝ) + 1) = 1 + (d:ℝ)⁻¹ := by field_simp
  simp only [homo]
  rw [smul_sub, smul_smul, hdd]
  module

/-- **Proposition 71(c)** (`o:prop:reduce`), first statement. Let `K ⊂ ℝ^d`, `d ≥ 1`, be compact
with positive volume (the paper: a convex body) and centroid `c`, and `K' = c - (K - c)/d`. Then
`U(K)` is `(d+1)`-completely mixable if and only if there is a joint law of `Y₁, …, Y_d`, each
uniformly distributed on `K`, under which `(Y₁ + ⋯ + Y_d)/d` is uniformly distributed on `K'`. -/
theorem reduce_c (hd : 1 ≤ d) {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hK0 : volume K ≠ 0)
    {c : Fin d → ℝ} (hc : ∫ x, x ∂(unifSet K) = c) :
    CompletelyMixable (d + 1) (unifSet K) ↔
      ∃ Q : Measure (Fin d → Fin d → ℝ), IsProbabilityMeasure Q ∧
        (∀ j, Q.map (fun y => y j) = unifSet K) ∧
        Q.map (fun y => (d:ℝ)⁻¹ • ∑ j, y j) = unifSet (homo c (-(d:ℝ)⁻¹) '' K) := by
  have hd0 : (d:ℝ) ≠ 0 := by have : (1:ℝ) ≤ d := by exact_mod_cast hd
                             linarith
  have hmean : Measurable fun y : Fin d → Fin d → ℝ => (d:ℝ)⁻¹ • ∑ j, y j := by
    fun_prop
  constructor
  · rintro ⟨P, hPp, ⟨s, hs⟩, hmarg⟩
    have hmarg : ∀ j, P.map (fun x => x j) = unifSet K := hmarg
    -- the constant sum is `(d+1) c`
    have hint : ∀ j, Integrable (fun x : Fin (d + 1) → Fin d → ℝ => x j) P := fun j => by
      have := unifSet_integrable hK hK0
      rw [← hmarg j] at this
      exact (integrable_map_measure this.aestronglyMeasurable
        (measurable_pi_apply j).aemeasurable).1 this
    have hs' : s = ((d:ℝ) + 1) • c := by
      have e1 : ∫ x, ∑ j, x j ∂P = s := by
        rw [integral_congr_ae hs, MeasureTheory.integral_const, probReal_univ, one_smul]
      have e2 : ∫ x, ∑ j, x j ∂P = ∑ j : Fin (d + 1), ∫ x, x j ∂P :=
        integral_finsetSum _ fun j _ => hint j
      have e3 : ∀ j : Fin (d + 1), ∫ x, x j ∂P = c := fun j => by
        rw [← hc, ← hmarg j, integral_map (measurable_pi_apply j).aemeasurable
          (aestronglyMeasurable_id (μ := Measure.map (fun x => x j) P))]
      rw [← e1, e2, Finset.sum_congr rfl fun j _ => e3 j, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℝ]; push_cast; rfl
    have htail : Measurable fun x : Fin (d + 1) → Fin d → ℝ => fun j : Fin d => x j.succ :=
      Measurable.of_eval fun j => measurable_pi_apply j.succ
    refine ⟨P.map fun x j => x j.succ, inferInstance,
      fun j => ?_, ?_⟩
    · rw [Measure.map_map (measurable_pi_apply j) htail]
      exact hmarg j.succ
    · rw [Measure.map_map hmean htail]
      have e : (fun y : Fin d → Fin d → ℝ => (d:ℝ)⁻¹ • ∑ j, y j) ∘ (fun x j => x j.succ) =ᵐ[P]
          homo c (-(d:ℝ)⁻¹) ∘ fun x => x 0 := by
        filter_upwards [hs] with x hx
        rw [Fin.sum_univ_succ, hs'] at hx
        simp only [Function.comp]
        rw [← mean_eq_homo hd0, ← hx, add_sub_cancel_left]
      rw [Measure.map_congr e, ← Measure.map_map (continuous_homo _ _).measurable
        (measurable_pi_apply 0), hmarg 0, map_unifSet_homo c (by simpa using hd0)]
  · rintro ⟨Q, hQp, hQm, hQmean⟩
    set x0 : (Fin d → Fin d → ℝ) → Fin d → ℝ := fun y => ((d:ℝ) + 1) • c - ∑ j, y j with hx0
    have hx0m : Measurable x0 :=
      measurable_const.sub (Finset.measurable_sum
        (f := fun (j : Fin d) (y : Fin d → Fin d → ℝ) => y j) Finset.univ
        fun j _ => measurable_pi_apply j)
    set F : (Fin d → Fin d → ℝ) → Fin (d + 1) → Fin d → ℝ := fun y => Fin.cons (x0 y) y with hF
    have hFm : Measurable F := by
      refine Measurable.of_eval fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hF] using hx0m
      · simpa [hF] using measurable_pi_apply j
    refine ⟨Q.map F, ⟨inferInstance, ⟨((d:ℝ) + 1) • c, ?_⟩,
      fun i => ?_⟩⟩
    · rw [ae_map_iff hFm.aemeasurable (measurableSet_eq_fun (Finset.measurable_sum
        (f := fun (j : Fin (d + 1)) (y : Fin (d + 1) → Fin d → ℝ) => y j) Finset.univ
        fun j _ => measurable_pi_apply j) measurable_const)]
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [hF, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hx0, sub_add_cancel]
    · rw [Measure.map_map (measurable_pi_apply i) hFm]
      refine Fin.cases ?_ (fun j => ?_) i
      · have e : (fun x : Fin (d + 1) → Fin d → ℝ => x 0) ∘ F =
            homo c (-(d:ℝ)) ∘ fun y => (d:ℝ)⁻¹ • ∑ j, y j := by
          ext1 y
          simp only [Function.comp, hF, Fin.cons_zero, hx0, homo]
          rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hd0]
          module
        rw [e, ← Measure.map_map (continuous_homo _ _).measurable hmean, hQmean,
          map_unifSet_homo c (by simpa using hd0), ← image_comp, homo_comp,
          show -(d:ℝ) * -(d:ℝ)⁻¹ = 1 by field_simp, homo_one, image_id]
      · have e : (fun x : Fin (d + 1) → Fin d → ℝ => x j.succ) ∘ F = fun y => y j := by
          ext1 y; simp [hF]
        rw [e, hQm j]

/-! ### Proposition 71(c) for `d = 2`: symmetric kernels -/

/-- The reflection `y ↦ 2 z - y` about `z`. -/
def refl (z y : Fin 2 → ℝ) : Fin 2 → ℝ := (2:ℝ) • z - y

lemma measurable_refl2 : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => refl p.1 p.2 := by
  unfold refl; fun_prop

lemma measurable_refl (z : Fin 2 → ℝ) : Measurable (refl z) := by unfold refl; fun_prop

/-- The kernel `z ↦ (κ z)` reflected about `z`. -/
noncomputable def reflKernel (κ : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ)) :
    Kernel (Fin 2 → ℝ) (Fin 2 → ℝ) :=
  (Kernel.deterministic id measurable_id ×ₖ κ).map fun p => refl p.1 p.2

instance (κ : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ)) [IsMarkovKernel κ] :
    IsMarkovKernel (reflKernel κ) := by
  unfold reflKernel; exact Kernel.IsMarkovKernel.map _ measurable_refl2

instance (κ : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (reflKernel κ) := by
  unfold reflKernel; infer_instance

lemma reflKernel_apply (κ : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ)) [IsSFiniteKernel κ]
    (z : Fin 2 → ℝ) : reflKernel κ z = (κ z).map (refl z) := by
  rw [reflKernel, Kernel.map_apply _ measurable_refl2, Kernel.prod_apply,
    Kernel.deterministic_apply, id, Measure.dirac_prod,
    Measure.map_map measurable_refl2 measurable_prodMk_left]
  rfl

lemma compProd_map_refl (μ : Measure (Fin 2 → ℝ)) [SFinite μ]
    (κ : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ)) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).map (fun p => (p.1, refl p.1 p.2)) = μ ⊗ₘ reflKernel κ := by
  have hg : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (p.1, refl p.1 p.2) :=
    measurable_fst.prodMk measurable_refl2
  ext t ht
  rw [Measure.map_apply hg ht, Measure.compProd_apply (hg ht), Measure.compProd_apply ht]
  refine lintegral_congr fun z => ?_
  rw [reflKernel_apply, Measure.map_apply (measurable_refl z) (measurable_prodMk_left ht)]
  rfl

lemma unifSet_isProb {d : ℕ} {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hK0 : volume K ≠ 0) :
    IsProbabilityMeasure (unifSet K) := by
  constructor
  rw [unifSet, smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    ENNReal.inv_mul_cancel hK0 hK.measure_lt_top.ne]

/-- The swap of two coordinates. -/
def sw (y : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ := ![y 1, y 0]

lemma measurable_sw : Measurable sw := by
  refine Measurable.of_eval fun i => ?_
  fin_cases i
  · exact measurable_pi_apply 1
  · exact measurable_pi_apply 0

lemma sw_sw (y : Fin 2 → Fin 2 → ℝ) : sw (sw y) = y := by
  ext i : 1; fin_cases i <;> rfl

/-- **Proposition 71(c)** (`o:prop:reduce`), the statement for `d = 2`: for a compact `K ⊂ ℝ²`
of positive volume with centroid `c` and `K' = c - (K - c)/2`, `U(K)` is `3`-completely mixable
if and only if `U(K) = ∫ S_z U(K')(dz)` for a Markov kernel `S` such that every `S_z` is symmetric
about `z`. -/
theorem reduce_c2 {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hK0 : volume K ≠ 0)
    {c : Fin 2 → ℝ} (hc : ∫ x, x ∂(unifSet K) = c) :
    CompletelyMixable 3 (unifSet K) ↔
      ∃ S : Kernel (Fin 2 → ℝ) (Fin 2 → ℝ), IsMarkovKernel S ∧
        (∀ z, (S z).map (refl z) = S z) ∧
        S ∘ₘ unifSet (homo c (-(2:ℝ)⁻¹) '' K) = unifSet K := by
  have hred := reduce_c (d := 2) (by norm_num) hK hK0 hc
  simp only [Nat.cast_ofNat] at hred
  rw [show (3:ℕ) = 2 + 1 from rfl, hred]
  set K' := homo c (-(2:ℝ)⁻¹) '' K with hK'
  have hUK := unifSet_isProb hK hK0
  have hUK' : IsProbabilityMeasure (unifSet K') := by
    rw [hK', ← map_unifSet_homo c (by norm_num) K]; infer_instance
  have hmean : Measurable fun y : Fin 2 → Fin 2 → ℝ => (2:ℝ)⁻¹ • ∑ j, y j := by fun_prop
  constructor
  · rintro ⟨Q, hQp, hQm, hQmean⟩
    set Q' : Measure (Fin 2 → Fin 2 → ℝ) := (2 : ENNReal)⁻¹ • (Q + Q.map sw) with hQ'
    have hQ'sw : Q'.map sw = Q' := by
      rw [hQ', Measure.map_smul, Measure.map_add _ _ measurable_sw,
        Measure.map_map measurable_sw measurable_sw]
      have : sw ∘ sw = id := funext sw_sw
      rw [this, Measure.map_id, add_comm]
      exact measurable_sw.aemeasurable
    have h2 : (2 : ENNReal)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
    have hQ'p : IsProbabilityMeasure Q' := by
      constructor
      rw [hQ', smul_apply, add_apply, Measure.map_apply measurable_sw MeasurableSet.univ,
        preimage_univ, measure_univ, smul_eq_mul, one_add_one_eq_two, h2]
    have hhalf : ∀ μ : Measure (Fin 2 → ℝ), (2 : ENNReal)⁻¹ • (μ + μ) = μ := fun μ => by
      rw [← two_smul ENNReal, smul_smul, h2, one_smul]
    have hmsw : (fun y : Fin 2 → Fin 2 → ℝ => (2:ℝ)⁻¹ • ∑ j, y j) ∘ sw =
        fun y => (2:ℝ)⁻¹ • ∑ j, y j := by
      ext1 y; simp [sw, Fin.sum_univ_two, add_comm]
    have hQ'mean : Q'.map (fun y => (2:ℝ)⁻¹ • ∑ j, y j) = unifSet K' := by
      rw [hQ', Measure.map_smul, Measure.map_add _ _ hmean, Measure.map_map hmean measurable_sw,
        hmsw, hQmean, hhalf]
      exact hmean.aemeasurable
    have hQ'0 : Q'.map (fun y => y 0) = unifSet K := by
      rw [hQ', Measure.map_smul, Measure.map_add _ _ (measurable_pi_apply 0),
        Measure.map_map (measurable_pi_apply 0) measurable_sw]
      have : (fun y : Fin 2 → Fin 2 → ℝ => y 0) ∘ sw = fun y => y 1 := rfl
      rw [this, hQm 0, hQm 1, hhalf]
      exact (measurable_pi_apply 0).aemeasurable
    set φ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
      fun y => ((2:ℝ)⁻¹ • ∑ j, y j, y 0) with hφdef
    have hφ : Measurable φ := hmean.prodMk (measurable_pi_apply 0)
    set ρ := Q'.map φ with hρ
    have hρfst : ρ.fst = unifSet K' := by
      rw [hρ, Measure.fst, Measure.map_map measurable_fst hφ]; exact hQ'mean
    have hρsnd : ρ.snd = unifSet K := by
      rw [hρ, Measure.snd, Measure.map_map measurable_snd hφ]; exact hQ'0
    have hg : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (p.1, refl p.1 p.2) :=
      measurable_fst.prodMk measurable_refl2
    have hρsym : ρ.map (fun p => (p.1, refl p.1 p.2)) = ρ := by
      rw [hρ, Measure.map_map hg hφ]
      have : (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (p.1, refl p.1 p.2)) ∘ φ = φ ∘ sw := by
        ext1 y
        simp only [Function.comp, hφdef, refl, sw, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Prod.mk.injEq]
        refine ⟨by rw [add_comm], ?_⟩
        ext i; simp
      rw [this, ← Measure.map_map hφ measurable_sw, hQ'sw]
    set κ := ρ.condKernel
    have hdis : ρ.fst ⊗ₘ κ = ρ := Measure.disintegrate ρ ρ.condKernel
    have hae : ∀ᵐ z ∂ρ.fst, reflKernel κ z = κ z := by
      have h1 : ρ = ρ.fst ⊗ₘ reflKernel κ := by
        calc ρ = ρ.map (fun p => (p.1, refl p.1 p.2)) := hρsym.symm
          _ = (ρ.fst ⊗ₘ κ).map (fun p => (p.1, refl p.1 p.2)) := by rw [hdis]
          _ = ρ.fst ⊗ₘ reflKernel κ := compProd_map_refl _ _
      exact eq_condKernel_of_measure_eq_compProd (reflKernel κ) h1
    set N := toMeasurable ρ.fst {z | reflKernel κ z ≠ κ z} with hNdef
    have hN : ρ.fst N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hae
    classical
    refine ⟨Kernel.piecewise (measurableSet_toMeasurable ρ.fst {z | reflKernel κ z ≠ κ z})
      (Kernel.deterministic id measurable_id) κ, inferInstance, fun z => ?_, ?_⟩
    · by_cases hz : z ∈ N
      · have hz' : z ∈ toMeasurable ρ.fst {z | reflKernel κ z ≠ κ z} := hz
        simp only [Kernel.piecewise_apply, hz', ↓reduceIte, Kernel.deterministic_apply, id]
        rw [Measure.map_dirac' (measurable_refl z)]
        congr 1; simp [refl, two_smul]
      · have hz' : z ∉ toMeasurable ρ.fst {z | reflKernel κ z ≠ κ z} := hz
        simp only [Kernel.piecewise_apply, hz', ↓reduceIte]
        have : z ∉ {z | reflKernel κ z ≠ κ z} := fun h => hz (subset_toMeasurable _ _ h)
        simp only [mem_ofPred_eq, not_not] at this
        rw [← reflKernel_apply, this]
    · rw [← hρfst, Measure.comp_congr (η := κ), ← Measure.snd_compProd, hdis, hρsnd]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz
      have hz' : z ∉ toMeasurable ρ.fst {z | reflKernel κ z ≠ κ z} := hz
      simp only [Kernel.piecewise_apply, hz', ↓reduceIte]
  · rintro ⟨S, hSm, hSsym, hSmix⟩
    have hrefl : reflKernel S = S := by
      ext1 z; rw [reflKernel_apply, hSsym z]
    have hF : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ![p.2, refl p.1 p.2] := by
      refine Measurable.of_eval fun i => ?_
      fin_cases i
      · exact measurable_snd
      · exact measurable_refl2
    refine ⟨(unifSet K' ⊗ₘ S).map fun p => ![p.2, refl p.1 p.2], inferInstance,
      fun j => ?_, ?_⟩
    · rw [Measure.map_map (measurable_pi_apply j) hF]
      fin_cases j
      · change (unifSet K' ⊗ₘ S).map Prod.snd = _
        rw [← Measure.snd, Measure.snd_compProd, hSmix]
      · change (unifSet K' ⊗ₘ S).map (Prod.snd ∘ fun p => (p.1, refl p.1 p.2)) = _
        rw [← Measure.map_map measurable_snd (measurable_fst.prodMk measurable_refl2),
          compProd_map_refl, hrefl, ← Measure.snd, Measure.snd_compProd, hSmix]
    · rw [Measure.map_map hmean hF]
      have e : ((fun y : Fin 2 → Fin 2 → ℝ => (2:ℝ)⁻¹ • ∑ j, y j) ∘
          fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ![p.2, refl p.1 p.2]) = Prod.fst := by
        ext1 p
        simp only [Function.comp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          refl]
        ext i; simp
      rw [e, ← Measure.fst, Measure.fst_compProd]

end Reduce

/-! ## Proposition 71(a): closedness under weak convergence -/

section Closed

open Filter Topology BoundedContinuousFunction

variable {d n : ℕ}

/-- The closedness step of **Proposition 71(a)** (`o:prop:reduce`): if probability measures
`F j` on `ℝ^d`, all concentrated on a common compact set `C`, converge weakly to `F∞` and every
`F j` is `n`-completely mixable, so is `F∞`. (Prokhorov's theorem gives a weakly convergent
subsequence of the complete mixes and of their sums.) -/
theorem completelyMixable_of_tendsto {F : ℕ → ProbabilityMeasure (Fin d → ℝ)}
    {Finf : ProbabilityMeasure (Fin d → ℝ)} (hF : Tendsto F atTop (𝓝 Finf))
    {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hsupp : ∀ j, (F j : Measure (Fin d → ℝ)) Cᶜ = 0)
    (hmix : ∀ j, CompletelyMixable n (F j : Measure (Fin d → ℝ))) :
    CompletelyMixable n (Finf : Measure (Fin d → ℝ)) := by
  choose P hP using hmix
  choose s hs using fun j => (hP j).2.1
  have hPp : ∀ j, IsProbabilityMeasure (P j) := fun j => (hP j).1
  have hmarg : ∀ j i, (P j).map (fun x => x i) = F j := fun j => (hP j).2.2
  set Pm : ℕ → ProbabilityMeasure (Fin n → Fin d → ℝ) := fun j => ⟨P j, hPp j⟩ with hPm
  set D : Set (Fin n → Fin d → ℝ) := univ.pi fun _ => C with hD
  have hDc : IsCompact D := isCompact_univ_pi fun _ => hC
  have hCm : MeasurableSet Cᶜ := hC.isClosed.measurableSet.compl
  have hDcompl : ∀ j, P j Dᶜ = 0 := fun j => by
    have e : Dᶜ = ⋃ i, (fun x : Fin n → Fin d → ℝ => x i) ⁻¹' Cᶜ := by
      ext x; simp [hD]
    rw [e]
    refine measure_iUnion_null fun i => ?_
    rw [← Measure.map_apply (measurable_pi_apply i) hCm, hmarg j i, hsupp j]
  set Ssum : Set (Fin d → ℝ) := (fun x : Fin n → Fin d → ℝ => ∑ i, x i) '' D with hSsum
  have hSc : IsCompact Ssum := hDc.image (by fun_prop)
  have hsS : ∀ j, s j ∈ Ssum := fun j => by
    have h1 : ∀ᵐ x ∂(P j), x ∈ D := by
      rw [ae_iff]; exact hDcompl j
    obtain ⟨x, hxD, hx⟩ := (h1.and (hs j)).exists
    exact ⟨x, hxD, hx⟩
  -- tightness and Prokhorov
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure (Fin n → Fin d → ℝ)) : Measure (Fin n → Fin d → ℝ)) |
        μ ∈ range Pm} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    refine fun ε _ => ⟨D, hDc, ?_⟩
    rintro μ ⟨ν, ⟨j, rfl⟩, rfl⟩
    simp [hPm, hDcompl j]
  have hK := (isCompact_closure_of_isTightMeasureSet htight).prod hSc
  obtain ⟨⟨π, s0⟩, -, φ, hφ, hlim⟩ :=
    hK.tendsto_subseq (x := fun j => (Pm j, s j)) fun j => ⟨subset_closure ⟨j, rfl⟩, hsS j⟩
  have hπ : Tendsto (fun k => Pm (φ k)) atTop (𝓝 π) := (continuous_fst.tendsto _).comp hlim
  have hs0 : Tendsto (fun k => s (φ k)) atTop (𝓝 s0) := (continuous_snd.tendsto _).comp hlim
  refine ⟨π, π.2, ⟨s0, ?_⟩, fun i => ?_⟩
  · -- the sum is constant
    let f : (Fin n → Fin d → ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
      ⟨fun x => min 1 ‖∑ i, x i - s0‖, by fun_prop⟩ 1 fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have := min_le_left 1 ‖∑ i, x i - s0‖
        have := min_le_left 1 ‖∑ i, y i - s0‖
        have : 0 ≤ min 1 ‖∑ i, x i - s0‖ := le_min zero_le_one (norm_nonneg _)
        have : 0 ≤ min 1 ‖∑ i, y i - s0‖ := le_min zero_le_one (norm_nonneg _)
        rw [abs_le]; constructor <;> linarith
    have hfv : ∀ x, f x = min 1 ‖∑ i, x i - s0‖ := fun x => rfl
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ) f
    have h2 : ∀ k, ∫ x, f x ∂((Pm (φ k) : ProbabilityMeasure _) : Measure _) =
        min 1 ‖s (φ k) - s0‖ := fun k => by
      have : (fun x => f x) =ᵐ[P (φ k)] fun _ => min 1 ‖s (φ k) - s0‖ := by
        filter_upwards [hs (φ k)] with x hx
        rw [hfv, hx]
      change ∫ x, f x ∂(P (φ k)) = _
      rw [integral_congr_ae this, MeasureTheory.integral_const, probReal_univ, one_smul]
    simp only [h2] at h1
    have h3 : Tendsto (fun k => min 1 ‖s (φ k) - s0‖) atTop (𝓝 0) := by
      have hc : Continuous fun y : Fin d → ℝ => min 1 ‖y - s0‖ := by fun_prop
      have := (hc.tendsto s0).comp hs0
      simpa [Function.comp_def] using this
    have h4 := tendsto_nhds_unique h1 h3
    have hf0 : 0 ≤ fun x => f x := fun x => by
      simp only [Pi.zero_apply, hfv]
      exact le_min zero_le_one (norm_nonneg _)
    have h5 : (fun x => f x) =ᵐ[(π : Measure _)] 0 :=
      (integral_eq_zero_iff_of_nonneg hf0 (f.integrable _)).1 h4
    filter_upwards [h5] with x hx
    rw [hfv, Pi.zero_apply] at hx
    have : ‖∑ i, x i - s0‖ = 0 := by
      by_contra hne
      have hpos : 0 < min 1 ‖∑ i, x i - s0‖ :=
        lt_min zero_lt_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · -- the marginals
    have hc := ((ProbabilityMeasure.continuous_map (continuous_apply i)).tendsto π).comp hπ
    have he : ∀ k, (Pm (φ k)).map (fun x => x i) = F (φ k) := fun k => by
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      exact hmarg (φ k) i
    simp only [Function.comp_def, he] at hc
    have := tendsto_nhds_unique hc (hF.comp hφ.tendsto_atTop)
    rw [← this, ProbabilityMeasure.toMeasure_map]

/-- `U(K)` as an element of `ProbabilityMeasure`. -/
def unifPM (K : Set (Fin d → ℝ)) (h : IsProbabilityMeasure (unifSet K)) :
    ProbabilityMeasure (Fin d → ℝ) := ⟨unifSet K, h⟩

/-- **Proposition 71(a)** (`o:prop:reduce`), first statement, for uniform distributions. Let
`K j` and `K∞` be compact sets of positive volume in `ℝ^d`, all contained in a compact set `C`,
such that `U(K j) → U(K∞)` weakly (hypothesis `hconv`; in the paper this follows from Hausdorff
convergence of convex bodies, since the volume of the symmetric difference tends to `0`). If every
`U(K j)` is `n`-completely mixable, so is `U(K∞)`. -/
theorem reduce_a {K : ℕ → Set (Fin d → ℝ)} {Kinf : Set (Fin d → ℝ)}
    (hKc : ∀ j, IsCompact (K j)) (hK0 : ∀ j, volume (K j) ≠ 0) (hKic : IsCompact Kinf)
    (hKi0 : volume Kinf ≠ 0) {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hsub : ∀ j, K j ⊆ C)
    (hconv : Tendsto (fun j => unifPM (K j) (unifSet_isProb (hKc j) (hK0 j))) atTop
      (𝓝 (unifPM Kinf (unifSet_isProb hKic hKi0))))
    (hmix : ∀ j, CompletelyMixable n (unifSet (K j))) :
    CompletelyMixable n (unifSet Kinf) := by
  refine completelyMixable_of_tendsto hconv hC (fun j => ?_) hmix
  change unifSet (K j) Cᶜ = 0
  rw [unifSet, smul_apply, Measure.restrict_apply hC.isClosed.measurableSet.compl]
  have : Cᶜ ∩ K j = ∅ := by
    ext x; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun hx hK => hx (hsub j hK)
  rw [this, measure_empty, smul_zero]

end Closed

end Bipyramid

end Mixes
