import Mixes.Symm
import Mixes.Bodies

/-!
# Symmetric bodies (Corollary 99, `st:cor:symm`)

Built on Proposition 98 (`Mixes.Symm`). The cited deep results are explicit hypotheses:
John's ellipsoid together with Ball's volume-ratio theorem (one hypothesis `hJB`), the
sufficiency part of Theorem 51 for balls (`hball`), Theorem 70 for the double cone (`hL3`), and
the Brunn–Minkowski inequality (`hBM`). The numerical inequalities are proved.

Main results.
* (a) `partA`, `partA_plane`, `partA_space`: centrally symmetric convex bodies; every even `n`
  and every odd `n ≥ 3·2^d/|B^d|`; in the plane every `n ≥ 2` other than `3`, in `ℝ³` every
  `n ≥ 2` other than `3, 5`.
* (b) `partB`, `partB_four`, `partB_five`: the cross-polytope of `ℝ^{m+1}`, modelled in
  `(Fin m → ℝ) × ℝ`; every even `n` and every odd `n ≥ 3 v_m`, with `v₃ = 3√3/π` and
  `v₄ = 64/(3π²)` computed.
* (c) `ball_core`, `dodecahedron`, `icosahedron`, `cell24`, `cell600`, `cell120`: every
  `n ≥ 2` other than `3`; the classical volumes, inradii and circumradii are hypotheses, the
  ratios `|K|/|B_r| < 5/3` are proved.
* (d) `partD`, `partD_plane`, `no_eigen_one_plane`: bodies with an affine symmetry of order `3`
  without fixed directions; in the plane every `n ≥ 3` other than `4`, with `u₂ = 3√3/π`.

Not formalised: the classification of regular polytopes and the claim for `d ≥ 6` in (c).
-/

open MeasureTheory Set Metric Module
open scoped ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes.SymmCor

/-! ### Ellipsoids and affine images -/

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The ellipsoid `e + T(B)`, with `B` the closed unit ball of `V`. -/
def ell (e : V) (T : V →ₗ[ℝ] V) : Set V := (fun x => T x + e) '' closedBall 0 1

/-- **Lemma 48 for complete mixability**: affine images of `U(K)` under bijective affine maps
are `n`-completely mixable when `U(K)` is. -/
theorem completelyMixable_image_affine {n : ℕ} {K : Set V} (h : CompletelyMixable n (unifSet K))
    {T : V →ₗ[ℝ] V} (hT : LinearMap.det T ≠ 0) (b : V) :
    CompletelyMixable n (unifSet ((fun x => T x + b) '' K)) := by
  obtain ⟨P, hP⟩ := h
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have := hP.map_add_hom T.toAddMonoidHom hTm (fun _ => b)
  refine ⟨_, (?_ : IsCompleteMix n _ (P.map (fun x i => b + T.toAddMonoidHom (x i))))⟩
  rw [← unifSet_map_affine K hT b]
  have e : (fun x => T x + b) = (fun x => b + T.toAddMonoidHom x) := by
    funext x; simp [add_comm]
  rw [e]; exact this

lemma isCompact_ell (e : V) (T : V →ₗ[ℝ] V) : IsCompact (ell e T) :=
  (isCompact_closedBall 0 1).image (T.continuous_of_finiteDimensional.add continuous_const)

lemma measurableSet_ell (e : V) (T : V →ₗ[ℝ] V) : MeasurableSet (ell e T) :=
  (isCompact_ell e T).isClosed.measurableSet

lemma volume_ell (e : V) (T : V →ₗ[ℝ] V) :
    volume (ell e T) = ENNReal.ofReal |LinearMap.det T| * volume (closedBall (0 : V) 1) :=
  volume_image_affine T e _

lemma volume_ell_ne_zero (e : V) {T : V →ₗ[ℝ] V} (hT : LinearMap.det T ≠ 0) :
    volume (ell e T) ≠ 0 := by
  rw [volume_ell]
  refine mul_ne_zero (by simpa using hT) (measure_closedBall_pos volume 0 one_pos).ne'

lemma pointReflection_apply' (c x : V) : AffineEquiv.pointReflection ℝ c x = c - x + c := by
  simp [AffineEquiv.pointReflection_apply, Equiv.pointReflection_apply]

/-- An ellipsoid is symmetric about its centre. -/
lemma pointReflection_ell (c : V) (T : V →ₗ[ℝ] V) :
    AffineEquiv.pointReflection ℝ c '' ell c T = ell c T := by
  have key : ∀ y ∈ ell c T, AffineEquiv.pointReflection ℝ c y ∈ ell c T := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨-b, by simpa using hb, ?_⟩
    simp only [map_neg, pointReflection_apply']; abel
  refine Subset.antisymm (image_subset_iff.2 key) fun y hy => ⟨_, key y hy, ?_⟩
  simp only [pointReflection_apply']; abel

/-- **Centring** (proof of Corollary 99(a)): if `K` is convex and symmetric about `c` and contains
the ellipsoid `e + T(B)`, then it contains its translate `c + T(B)`, the Minkowski average of
`E` and `2c - E`. -/
lemma ell_center_subset {K : Set V} {c e : V} {T : V →ₗ[ℝ] V} (hconv : Convex ℝ K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K) (hE : ell e T ⊆ K) : ell c T ⊆ K := by
  rintro _ ⟨b, hb, rfl⟩
  have h1 : T b + e ∈ K := hE ⟨b, hb, rfl⟩
  have h2 : T (-b) + e ∈ K := hE ⟨-b, by simpa using hb, rfl⟩
  have h3 : c - (T (-b) + e) + c ∈ K := by
    rw [← hKs]; exact ⟨_, h2, pointReflection_apply' c _⟩
  have := hconv h1 h3 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  convert this using 1
  simp only [map_neg]
  module

end General

/-! ### Part (a): centrally symmetric bodies -/

section PartA

variable {d : ℕ}

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- **Corollary 99(a)**, for `ℝ^d` (`EuclideanSpace ℝ (Fin d)`). Let `K` be a measurable convex
set of finite volume, symmetric about `c`. Cited results, as hypotheses:
* `hJB` (John's theorem on the existence of an ellipsoid of maximal volume in `K`, with Ball's
  theorem that among centrally symmetric bodies the cube has the largest volume ratio, whose
  value `2^d/|B^d|` is attained by `[-1,1]^d`): `K` contains an ellipsoid `e + T(B)`, `T`
  invertible, with `|K| ≤ (2^d/|B^d|) |e + T(B)|`;
* `hball` (sufficiency in Theorem 51): `U(B^d)` is `3`-completely mixable.
Then `U(K)` is `n`-completely mixable for every even `n ≥ 2` and every odd `n ≥ 3·2^d/|B^d|`. -/
theorem partA {K : Set (E d)} {c : E d} (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hconv : Convex ℝ K) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : E d) (T : (E d) →ₗ[ℝ] (E d)), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ d / (volume (closedBall (0 : E d) 1)).toReal *
        (volume (ell e T)).toReal)
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E d) 1))) :
    (∀ n : ℕ, Even n → n ≠ 0 → CompletelyMixable n (unifSet K)) ∧
      (∀ n : ℕ, Odd n → 3 * 2 ^ d / (volume (closedBall (0 : E d) 1)).toReal ≤ n →
        CompletelyMixable n (unifSet K)) := by
  obtain ⟨e, T, hT, hsub, hratio⟩ := hJB
  have hLK := ell_center_subset hconv hKs hsub
  have hvol : volume (ell c T) = volume (ell e T) := by rw [volume_ell, volume_ell]
  obtain ⟨hev, hodd⟩ := completelyMixable_centralSymm hK (measurableSet_ell c T) hLK hKs
    (pointReflection_ell c T) (volume_ell_ne_zero c hT) hKfin
    (completelyMixable_image_affine hball hT c)
  refine ⟨hev, fun n hn hle => hodd n hn ?_⟩
  rw [hvol]
  set r := 2 ^ d / (volume (closedBall (0 : E d) 1)).toReal
  have hr : 0 ≤ r := by positivity
  have h3 : 3 * r ≤ n := by simpa [r, mul_div_assoc] using hle
  have hL := ENNReal.toReal_nonneg (a := volume (ell e T))
  nlinarith

lemma volume_closedBall_two : (volume (closedBall (0 : E 2) 1)).toReal = Real.pi := by
  rw [EuclideanSpace.volume_closedBall_fin_two]; simp [Real.pi_pos.le]

lemma volume_closedBall_three :
    (volume (closedBall (0 : E 3) 1)).toReal = Real.pi * 4 / 3 := by
  rw [EuclideanSpace.volume_closedBall_fin_three]; simp; positivity

/-- `3 · 2²/|B²| = 12/π < 5`. -/
lemma bound_two : 3 * 2 ^ 2 / Real.pi < 5 := by
  rw [div_lt_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]

/-- `3 · 2³/|B³| = 18/π < 7`. -/
lemma bound_three : 3 * 2 ^ 3 / (Real.pi * 4 / 3) < 7 := by
  rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_gt_d2]

/-- **Corollary 99(a) in the plane**: every `n ≥ 2` other than `3`. -/
theorem partA_plane {K : Set (E 2)} {c : E 2} (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hconv : Convex ℝ K) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : E 2) (T : (E 2) →ₗ[ℝ] (E 2)), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ 2 / (volume (closedBall (0 : E 2) 1)).toReal *
        (volume (ell e T)).toReal)
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 2) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) := by
  obtain ⟨hev, hodd⟩ := partA hK hKfin hconv hKs hJB hball
  intro n hn h3
  rcases Nat.even_or_odd n with he | ho
  · exact hev n he (by omega)
  · refine hodd n ho ?_
    rw [volume_closedBall_two]
    have : (5 : ℝ) ≤ n := by
      obtain ⟨k, rfl⟩ := ho
      have : 5 ≤ 2 * k + 1 := by omega
      exact_mod_cast this
    linarith [bound_two]

/-- **Corollary 99(a) in `ℝ³`**: every `n ≥ 2` other than `3` and `5`. -/
theorem partA_space {K : Set (E 3)} {c : E 3} (hK : MeasurableSet K) (hKfin : volume K ≠ ∞)
    (hconv : Convex ℝ K) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : E 3) (T : (E 3) →ₗ[ℝ] (E 3)), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ 3 / (volume (closedBall (0 : E 3) 1)).toReal *
        (volume (ell e T)).toReal)
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 3) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → n ≠ 5 → CompletelyMixable n (unifSet K) := by
  obtain ⟨hev, hodd⟩ := partA hK hKfin hconv hKs hJB hball
  intro n hn h3 h5
  rcases Nat.even_or_odd n with he | ho
  · exact hev n he (by omega)
  · refine hodd n ho ?_
    rw [volume_closedBall_three]
    have : (7 : ℝ) ≤ n := by
      obtain ⟨k, rfl⟩ := ho
      have : 7 ≤ 2 * k + 1 := by omega
      exact_mod_cast this
    linarith [bound_three]

end PartA

/-! ### Part (c): regular polytopes with an inscribed ball as the core -/

section PartC

variable {d : ℕ}

local notation "E" d => EuclideanSpace ℝ (Fin d)

lemma ell_smul_id (c : E d) {r : ℝ} (hr : 0 < r) :
    ell c (r • LinearMap.id) = closedBall c r := by
  ext y
  simp only [ell, mem_image, mem_closedBall, dist_eq_norm, sub_zero, LinearMap.smul_apply,
    LinearMap.id_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg b]
  · intro hy
    refine ⟨r⁻¹ • (y - c), ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
      calc r⁻¹ * ‖y - c‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]

/-- **The ball as the core** (proof of Corollary 99(c)): if `K` is symmetric about `c`, contains
the ball `B(c, r)` and `|K| ≤ (5/3)|B(c, r)|`, then (given Theorem 51) `U(K)` is `n`-completely
mixable for every `n ≥ 2` other than `3`. -/
theorem ball_core {K : Set (E d)} {c : E d} {r : ℝ} (hr : 0 < r) (hK : MeasurableSet K)
    (hKfin : volume K ≠ ∞) (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c r ⊆ K)
    (hvol : (volume K).toReal ≤ 5 / 3 * (volume (closedBall c r)).toReal)
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E d) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) := by
  have hT : LinearMap.det (r • LinearMap.id : (E d) →ₗ[ℝ] (E d)) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]; exact pow_ne_zero _ hr.ne'
  have hL3 := completelyMixable_image_affine hball hT c
  have hLs := pointReflection_ell c (r • LinearMap.id : (E d) →ₗ[ℝ] (E d))
  change CompletelyMixable 3 (unifSet (ell c _)) at hL3
  rw [ell_smul_id c hr] at hL3 hLs
  obtain ⟨hev, hodd⟩ := completelyMixable_centralSymm hK measurableSet_closedBall hBK hKs hLs
    (measure_closedBall_pos volume c hr).ne' hKfin hL3
  intro n hn h3
  rcases Nat.even_or_odd n with he | ho
  · exact hev n he (by omega)
  · refine hodd n ho ?_
    have : (5 : ℝ) ≤ n := by
      obtain ⟨k, rfl⟩ := ho
      have : 5 ≤ 2 * k + 1 := by omega
      exact_mod_cast this
    have := ENNReal.toReal_nonneg (a := volume (closedBall c r))
    nlinarith

/-- Volume ratio of two concentric balls: `B(c, r) ⊆ K ⊆ B(c, R)` gives
`|K| ≤ (R/r)^d |B(c, r)|`. -/
lemma volume_le_of_balls {K : Set (E d)} {c : E d} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hKR : K ⊆ closedBall c R) :
    (volume K).toReal ≤ (R / r) ^ d * (volume (closedBall c r)).toReal := by
  have hR : 0 ≤ R := hr.le.trans hrR
  have hfin : volume (closedBall c R) ≠ ∞ := measure_closedBall_lt_top.ne
  have h1 := ENNReal.toReal_mono hfin (measure_mono hKR)
  rw [Measure.addHaar_closedBall' _ _ hR, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h1
  rw [Measure.addHaar_closedBall' _ _ hr.le, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← mul_assoc, ← mul_pow,
    div_mul_cancel₀ R hr.ne']
  exact h1

lemma volume_closedBall_three' (c : E 3) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (closedBall c ρ)).toReal = ρ ^ 3 * (Real.pi * 4 / 3) := by
  rw [EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hρ, ENNReal.toReal_ofReal (by positivity)]

lemma volume_closedBall_four (c : E 4) : (volume (closedBall c 1)).toReal = Real.pi ^ 2 / 2 := by
  rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp)]
  simp [Nat.factorial]; positivity

lemma le_sqrt_of {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) : x ≤ √y := by
  calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ √y := Real.sqrt_le_sqrt h

lemma sqrt5_bounds : 2.236 ≤ √5 ∧ √5 ≤ 2.2361 := by
  refine ⟨le_sqrt_of (by norm_num) (by norm_num), Real.sqrt_le_iff.2 ⟨by norm_num,
    by norm_num⟩⟩

/-- The regular dodecahedron with edge `a` (volume `(15 + 7√5)a³/4`, inradius
`a(250 + 110√5)^{1/2}/20`) has volume at most `5/3` of its inscribed ball (about `1.325`). -/
lemma dodecahedron_ratio {a : ℝ} (ha : 0 < a) :
    (15 + 7 * √5) * a ^ 3 / 4 ≤
      5 / 3 * ((a * √(250 + 110 * √5) / 20) ^ 3 * (Real.pi * 4 / 3)) := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  set q := √(250 + 110 * √5)
  have hq : 22.2 ≤ q := le_sqrt_of (by norm_num) (by nlinarith)
  have hq3 : 22.2 ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
  have hpi := Real.pi_gt_d2
  have hpq : 3.14 * 22.2 ^ 3 ≤ Real.pi * q ^ 3 :=
    mul_le_mul hpi.le hq3 (by norm_num) Real.pi_pos.le
  have core : (15 + 7 * √5) / 4 ≤ 5 / 3 * ((q / 20) ^ 3 * (Real.pi * 4 / 3)) := by
    have : 5 / 3 * ((q / 20) ^ 3 * (Real.pi * 4 / 3)) = Real.pi * q ^ 3 / 3600 := by ring
    rw [this]; nlinarith
  calc (15 + 7 * √5) * a ^ 3 / 4 = (15 + 7 * √5) / 4 * a ^ 3 := by ring
    _ ≤ 5 / 3 * ((q / 20) ^ 3 * (Real.pi * 4 / 3)) * a ^ 3 :=
        mul_le_mul_of_nonneg_right core (by positivity)
    _ = _ := by ring

/-- The regular icosahedron with edge `a` (volume `5(3 + √5)a³/12`, inradius
`a(3√3 + √15)/12`): ratio about `1.207`. -/
lemma icosahedron_ratio {a : ℝ} (ha : 0 < a) :
    5 * (3 + √5) * a ^ 3 / 12 ≤
      5 / 3 * ((a * (3 * √3 + √15) / 12) ^ 3 * (Real.pi * 4 / 3)) := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have h3 : 1.732 ≤ √3 := le_sqrt_of (by norm_num) (by norm_num)
  have h15 : 3.872 ≤ √15 := le_sqrt_of (by norm_num) (by norm_num)
  set q := 3 * √3 + √15
  have hq : 9.068 ≤ q := by simp only [q]; linarith
  have hq3 : 9.068 ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
  have hpi := Real.pi_gt_d2
  have hpq : 3.14 * 9.068 ^ 3 ≤ Real.pi * q ^ 3 :=
    mul_le_mul hpi.le hq3 (by norm_num) Real.pi_pos.le
  have core : 5 * (3 + √5) / 12 ≤ 5 / 3 * ((q / 12) ^ 3 * (Real.pi * 4 / 3)) := by
    have : 5 / 3 * ((q / 12) ^ 3 * (Real.pi * 4 / 3)) = Real.pi * q ^ 3 * (5 / 3888) := by ring
    rw [this]; nlinarith
  calc 5 * (3 + √5) * a ^ 3 / 12 = 5 * (3 + √5) / 12 * a ^ 3 := by ring
    _ ≤ 5 / 3 * ((q / 12) ^ 3 * (Real.pi * 4 / 3)) * a ^ 3 :=
        mul_le_mul_of_nonneg_right core (by positivity)
    _ = _ := by ring

/-- The `24`-cell (volume `8`, inradius `1`): `16/π² < 5/3`. -/
lemma cell24_ratio : (8 : ℝ) ≤ 5 / 3 * (Real.pi ^ 2 / 2) := by
  nlinarith [Real.pi_gt_d2]

/-- The inradius of the `600`-cell with circumradius `1`: `1 - 3/(8φ²) = (7 + 3√5)/16`. -/
lemma cell600_inradius_sq :
    1 - 3 / (8 * ((1 + √5) / 2) ^ 2) = (7 + 3 * √5) / 16 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 1 + √5 := by positivity
  field_simp
  nlinarith [h5]

/-- `r⁻⁴ = 128/(47 + 21√5) < 5/3` (indeed `< 1.37`) for `r² = (7 + 3√5)/16`. -/
lemma cell600_ratio :
    (1 / √((7 + 3 * √5) / 16)) ^ 4 = 128 / (47 + 21 * √5) ∧
      128 / (47 + 21 * √5) < 5 / 3 ∧ 128 / (47 + 21 * √5) < 1.37 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr2 : √((7 + 3 * √5) / 16) ^ 2 = (7 + 3 * √5) / 16 := Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : (1 / √((7 + 3 * √5) / 16)) ^ 4 = 1 / ((7 + 3 * √5) / 16) ^ 2 := by
      rw [show (1 / √((7 + 3 * √5) / 16)) ^ 4 = 1 / (√((7 + 3 * √5) / 16) ^ 2) ^ 2 by ring,
        hr2]
    rw [this]
    field_simp
    nlinarith [h5]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- **Corollary 99(c), dodecahedron.** Given its classical volume and inradius (as hypotheses)
and Theorem 51: every `n ≥ 2` other than `3`. -/
theorem dodecahedron {K : Set (E 3)} {c : E 3} {a : ℝ} (ha : 0 < a) (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c (a * √(250 + 110 * √5) / 20) ⊆ K)
    (hvolK : volume K = ENNReal.ofReal ((15 + 7 * √5) * a ^ 3 / 4))
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 3) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  ball_core (by positivity) hK (by rw [hvolK]; exact ENNReal.ofReal_ne_top) hKs hBK (by
    rw [hvolK, ENNReal.toReal_ofReal (by positivity), volume_closedBall_three' c (by positivity)]
    exact dodecahedron_ratio ha) hball

/-- **Corollary 99(c), icosahedron.** -/
theorem icosahedron {K : Set (E 3)} {c : E 3} {a : ℝ} (ha : 0 < a) (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c (a * (3 * √3 + √15) / 12) ⊆ K)
    (hvolK : volume K = ENNReal.ofReal (5 * (3 + √5) * a ^ 3 / 12))
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 3) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  ball_core (by positivity) hK (by rw [hvolK]; exact ENNReal.ofReal_ne_top) hKs hBK (by
    rw [hvolK, ENNReal.toReal_ofReal (by positivity), volume_closedBall_three' c (by positivity)]
    exact icosahedron_ratio ha) hball

/-- **Corollary 99(c), `24`-cell** (volume `8`, inradius `1`, as hypotheses). -/
theorem cell24 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K) (hBK : closedBall c 1 ⊆ K)
    (hvolK : volume K = 8) (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 4) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  ball_core one_pos hK (by rw [hvolK]; exact ENNReal.ofNat_ne_top) hKs hBK (by
    rw [hvolK, volume_closedBall_four]; simpa using cell24_ratio) hball

/-- **Corollary 99(c), `600`-cell**: with circumradius `1` it contains the ball of radius
`r = ((7 + 3√5)/16)^{1/2}` about its centre (its inradius, as a hypothesis) and lies in the unit
ball, so `|K|/|B_r| ≤ r⁻⁴ < 5/3`. -/
theorem cell600 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c √((7 + 3 * √5) / 16) ⊆ K) (hKB : K ⊆ closedBall c 1)
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 4) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) := by
  obtain ⟨e1, e2, -⟩ := cell600_ratio
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have hr : 0 < √((7 + 3 * √5) / 16) := Real.sqrt_pos.2 (by positivity)
  have hr1 : √((7 + 3 * √5) / 16) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  refine ball_core hr hK (ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hKB))
    hKs hBK ?_ hball
  have := volume_le_of_balls hr hr1 hKB
  rw [e1] at this
  have := ENNReal.toReal_nonneg (a := volume (closedBall c √((7 + 3 * √5) / 16)))
  nlinarith

/-- **Corollary 99(c), `120`-cell**: the polar body of the `600`-cell, with inradius `1` and
circumradius `1/r` (as hypotheses). -/
theorem cell120 {K : Set (E 4)} {c : E 4} (hK : MeasurableSet K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hBK : closedBall c 1 ⊆ K) (hKB : K ⊆ closedBall c (1 / √((7 + 3 * √5) / 16)))
    (hball : CompletelyMixable 3 (unifSet (closedBall (0 : E 4) 1))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) := by
  obtain ⟨e1, e2, -⟩ := cell600_ratio
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  have hr : 0 < √((7 + 3 * √5) / 16) := Real.sqrt_pos.2 (by positivity)
  have hr1 : √((7 + 3 * √5) / 16) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hR1 : 1 ≤ 1 / √((7 + 3 * √5) / 16) := by rw [le_div_iff₀ hr]; linarith
  refine ball_core one_pos hK (ne_top_of_le_ne_top measure_closedBall_lt_top.ne
    (measure_mono hKB)) hKs hBK ?_ hball
  have := volume_le_of_balls one_pos hR1 hKB
  rw [div_one, e1] at this
  have := ENNReal.toReal_nonneg (a := volume (closedBall c (1 : ℝ)))
  nlinarith

end PartC

/-! ### Part (d): an affine symmetry of order `3` -/

section PartD

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- The Minkowski average `(X + Y + Z)/3`. -/
def avg3 (X Y Z : Set V) : Set V :=
  (fun p : V × V × V => (1 / 3 : ℝ) • p.1 + (1 / 3 : ℝ) • p.2.1 + (1 / 3 : ℝ) • p.2.2) ''
    (X ×ˢ Y ×ˢ Z)

lemma mem_avg3 {X Y Z : Set V} {x y z : V} (hx : x ∈ X) (hy : y ∈ Y) (hz : z ∈ Z) :
    (1 / 3 : ℝ) • x + (1 / 3 : ℝ) • y + (1 / 3 : ℝ) • z ∈ avg3 X Y Z :=
  ⟨(x, y, z), ⟨hx, hy, hz⟩, rfl⟩

lemma isCompact_avg3 {X Y Z : Set V} (hX : IsCompact X) (hY : IsCompact Y) (hZ : IsCompact Z) :
    IsCompact (avg3 X Y Z) :=
  (hX.prod (hY.prod hZ)).image (by fun_prop)

lemma affine_lin (A : V ≃ᵃ[ℝ] V) (x : V) : A x = A.linear x + A 0 := by
  simpa using affine_apply_eq A x 0

lemma affine_avg3 (A : V ≃ᵃ[ℝ] V) (x y z : V) :
    A ((1 / 3 : ℝ) • x + (1 / 3 : ℝ) • y + (1 / 3 : ℝ) • z) =
      (1 / 3 : ℝ) • A x + (1 / 3 : ℝ) • A y + (1 / 3 : ℝ) • A z := by
  rw [affine_lin A ((1 / 3 : ℝ) • x + (1 / 3 : ℝ) • y + (1 / 3 : ℝ) • z), affine_lin A x,
    affine_lin A y, affine_lin A z]
  simp only [map_add, map_smul]; module

/-- Symmetry about a point, in the form `x ∈ X → 2p - x ∈ X`. -/
def SymmAbout (X : Set V) (p : V) : Prop := ∀ x ∈ X, (2 : ℝ) • p - x ∈ X

lemma symmAbout_image (A : V ≃ᵃ[ℝ] V) {X : Set V} {p : V} (h : SymmAbout X p) :
    SymmAbout (A '' X) (A p) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨_, h y hy, ?_⟩
  rw [affine_lin A ((2 : ℝ) • p - y), affine_lin A p, affine_lin A y]
  simp only [map_sub, map_smul]; module

lemma symmAbout_avg3 {X Y Z : Set V} {p q r : V} (hX : SymmAbout X p) (hY : SymmAbout Y q)
    (hZ : SymmAbout Z r) :
    SymmAbout (avg3 X Y Z) ((1 / 3 : ℝ) • p + (1 / 3 : ℝ) • q + (1 / 3 : ℝ) • r) := by
  rintro _ ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
  refine ⟨((2 : ℝ) • p - x, (2 : ℝ) • q - y, (2 : ℝ) • r - z),
    ⟨hX x hx, hY y hy, hZ z hz⟩, ?_⟩
  simp only; module

lemma symmAbout_ell (e : V) (T : V →ₗ[ℝ] V) : SymmAbout (ell e T) e := by
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨-b, by simpa using hb, ?_⟩
  simp only [map_neg]; module

lemma pointReflection_of_symmAbout {X : Set V} {p : V} (h : SymmAbout X p) :
    AffineEquiv.pointReflection ℝ p '' X = X := by
  have e : ∀ x, AffineEquiv.pointReflection ℝ p x = (2 : ℝ) • p - x := fun x => by
    rw [pointReflection_apply']; module
  refine Subset.antisymm (fun _ ⟨x, hx, hxe⟩ => hxe ▸ (e x).symm ▸ h x hx)
    fun x hx => ⟨_, h x hx, by rw [e]; module⟩

lemma volume_image_eq (A : V ≃ᵃ[ℝ] V) (hA : MeasurePreserving A volume volume) {X : Set V}
    (hX : IsCompact X) : volume (A '' X) = volume X := by
  have hc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  rw [← hA.measure_preimage (hX.image hc).isClosed.measurableSet.nullMeasurableSet,
    A.injective.preimage_image]

/-- Even complete mixes of a body symmetric about `c`, by pairs `(Y, 2c - Y)`. -/
lemma completelyMixable_even {L : Set V} {c : V} (hL : MeasurableSet L)
    (hLs : AffineEquiv.pointReflection ℝ c '' L = L) (hL0 : volume L ≠ 0)
    (hLfin : volume L ≠ ∞) {j : ℕ} (hj : j ≠ 0) : CompletelyMixable (j * 2) (unifSet L) := by
  set B := AffineEquiv.pointReflection ℝ c
  have hB2 : (⇑B)^[2] = id := by
    funext x
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact AffineEquiv.pointReflection_involutive ℝ c x
  have h1 : ∀ v, B.linear v = v → v = 0 := by
    intro v hv
    have hlin : B.linear v = -v := by
      have h := affine_lin B v
      have e1 : B v = c - v + c := pointReflection_apply' c v
      have e0 : B 0 = c + c := by rw [pointReflection_apply']; abel
      rw [e1, e0] at h
      have : B.linear v = c - v + c - (c + c) := by rw [h]; abel
      rw [this]; abel
    rw [hlin] at hv
    have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rw 1 [← hv]; exact neg_add_cancel v
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  exact completelyMixable_mul B two_ne_zero hB2 h1 hL hLs hL0 hLfin hj

/-- **Corollary 99(d).** Let `K` be a compact convex set with `A(K) = K` for an affine bijection
`A` with `A³ = id` whose linear part has no eigenvalue `1`. Cited results, as hypotheses:
* `hJB` (John's ellipsoid of maximal volume with Ball's theorem that the simplex has the
  largest volume ratio, `u = u_d`): `K` contains an ellipsoid `e + T(B)` with
  `|K| ≤ u |e + T(B)|`;
* `hBM` (the Brunn–Minkowski inequality, in the form `|(X + Y + Z)/3| ≥ min(|X|, |Y|, |Z|)` for
  nonempty compact sets).
Then `U(K)` is `n`-completely mixable for every positive multiple `n` of `3`, every
`n ≡ 2 (mod 3)` with `n ≥ 2u`, and every `n ≡ 1 (mod 3)` with `n ≥ 4u`. -/
theorem partD {K : Set V} (hK : IsCompact K) (hconv : Convex ℝ K) (A : V ≃ᵃ[ℝ] V)
    (hm : (⇑A)^[3] = id) (h1 : ∀ v, A.linear v = v → v = 0) (hAK : A '' K = K) {u : ℝ}
    (hJB : ∃ (e : V) (T : V →ₗ[ℝ] V), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ u * (volume (ell e T)).toReal)
    (hBM : ∀ X Y Z : Set V, IsCompact X → IsCompact Y → IsCompact Z → X.Nonempty →
      Y.Nonempty → Z.Nonempty → min (volume X) (min (volume Y) (volume Z)) ≤
        volume (avg3 X Y Z)) :
    (∀ j : ℕ, j ≠ 0 → CompletelyMixable (3 * j) (unifSet K)) ∧
    (∀ n : ℕ, n % 3 = 2 → 2 * u ≤ n → CompletelyMixable n (unifSet K)) ∧
    (∀ n : ℕ, n % 3 = 1 → 4 * u ≤ n → CompletelyMixable n (unifSet K)) := by
  obtain ⟨e, T, hT, hEK, hratio⟩ := hJB
  obtain ⟨c, hc, -⟩ := exists_unique_fixed A h1
  have hA := measurePreserving_affine A three_ne_zero hm
  have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
  have hA3 : ∀ z, A (A (A z)) = z := fun z => by
    have := congrFun hm z; simpa [Function.iterate_succ] using this
  have hmaps : ∀ x ∈ K, A x ∈ K := fun x hx => hAK ▸ mem_image_of_mem A hx
  set E := ell e T
  have hE := isCompact_ell e T
  set L := avg3 E (A '' E) (A '' (A '' E))
  have hLc : IsCompact L := isCompact_avg3 hE (hE.image hAc) ((hE.image hAc).image hAc)
  have hLm : MeasurableSet L := hLc.isClosed.measurableSet
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKfin : volume K ≠ ∞ := hK.measure_lt_top.ne
  -- `L ⊆ K`
  have hLK : L ⊆ K := by
    rintro _ ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
    have hx' := hEK hx
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hz
    have hy'' := hmaps _ (hEK hy')
    have hz'' := hmaps _ (hmaps _ (hEK hz'))
    have hyz := hconv hy'' hz'' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have := hconv hx' hyz (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num)
    convert this using 1
    simp only; module
  -- `A(L) = L`
  have hAL : A '' L = L := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩, rfl⟩
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hz
      have := mem_avg3 (X := E) (Y := A '' E) (Z := A '' (A '' E)) hz'
        (mem_image_of_mem A hx) (mem_image_of_mem A (mem_image_of_mem A hy'))
      simp only [affine_avg3, hA3]
      convert this using 1
      abel
    · rintro _ ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hz
      refine ⟨_, mem_avg3 (X := E) (Y := A '' E) (Z := A '' (A '' E)) hy'
        (mem_image_of_mem A hz') (mem_image_of_mem A (mem_image_of_mem A hx)), ?_⟩
      simp only [affine_avg3, hA3]
      abel
  -- `L` is symmetric about `c`
  have hsum : (1 / 3 : ℝ) • e + (1 / 3 : ℝ) • A e + (1 / 3 : ℝ) • A (A e) = c := by
    have := orbit_sum A hm h1 hc e
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Function.iterate_zero, id,
      Function.iterate_succ, Function.comp_apply, zero_add] at this
    have h3 : (3 : ℝ) • c = e + A e + A (A e) := by
      rw [this, ← Nat.cast_smul_eq_nsmul ℝ]; norm_num
    rw [← smul_add, ← smul_add, ← h3, smul_smul]; norm_num
  have hLs : AffineEquiv.pointReflection ℝ c '' L = L := by
    apply pointReflection_of_symmAbout
    rw [← hsum]
    exact symmAbout_avg3 (symmAbout_ell e T) (symmAbout_image A (symmAbout_ell e T))
      (symmAbout_image A (symmAbout_image A (symmAbout_ell e T)))
  -- volumes
  have hvE : volume E ≤ volume L := by
    have hne : E.Nonempty := ⟨T 0 + e, 0, by simp, rfl⟩
    have := hBM E (A '' E) (A '' (A '' E)) hE (hE.image hAc) ((hE.image hAc).image hAc) hne
      (hne.image A) ((hne.image A).image A)
    rwa [volume_image_eq A hA ((hE.image hAc)), volume_image_eq A hA hE, min_self,
      min_self] at this
  have hE0 : volume E ≠ 0 := volume_ell_ne_zero e hT
  have hL0 : volume L ≠ 0 := fun h => hE0 (le_antisymm (hvE.trans h.le) bot_le)
  have hK0 : volume K ≠ 0 := fun h => hL0 (measure_mono_null hLK h)
  have hLfin : volume L ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hLK)
  have hEfin : volume E ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hEK)
  have hκ : 0 < (volume K).toReal := ENNReal.toReal_pos hK0 hKfin
  have hvE' : (volume E).toReal ≤ (volume L).toReal := ENNReal.toReal_mono hLfin hvE
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEfin
  have hLK' : (volume L).toReal ≤ (volume K).toReal := ENNReal.toReal_mono hKfin (measure_mono hLK)
  have hu : 0 ≤ u := by
    by_contra hneg; push Not at hneg; nlinarith
  have hKL : (volume K).toReal ≤ u * (volume L).toReal :=
    hratio.trans (mul_le_mul_of_nonneg_left hvE' hu)
  have hL2 := completelyMixable_even hLm hLs hL0 hLfin (j := 1) one_ne_zero
  have hL4 := completelyMixable_even hLm hLs hL0 hLfin (j := 2) two_ne_zero
  have heq : (volume K).toReal ≤ (volume L).toReal → unifSet L = unifSet K := fun h =>
    unifSet_eq_of_volume_le hLm hLK hKfin ((ENNReal.toReal_le_toReal hKfin hLfin).1 h)
  refine ⟨fun j hj => ?_, fun n hn h2 => ?_, fun n hn h4 => ?_⟩
  · rw [mul_comm]
    exact completelyMixable_mul A three_ne_zero hm h1 hKm hAK hK0 hKfin hj
  · obtain ⟨j, rfl⟩ : ∃ j, n = j * 3 + 2 := ⟨n / 3, by omega⟩
    have hc2 : (2 : ℝ) * (volume K).toReal ≤ ((j * 3 + 2 : ℕ) : ℝ) * (volume L).toReal := by
      nlinarith
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [← heq (by push_cast at hc2; linarith)]; simpa using hL2
    · exact completelyMixable_add A three_ne_zero hm h1 hKm hLm hLK hAK hAL hL0 hKfin hL2
        hj.ne' hc2
  · obtain ⟨j, rfl⟩ : ∃ j, n = j * 3 + 1 := ⟨n / 3, by omega⟩
    have hc4 : (4 : ℝ) * (volume K).toReal ≤ ((j * 3 + 1 : ℕ) : ℝ) * (volume L).toReal := by
      nlinarith
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · push_cast at hc4; nlinarith
      · rw [← heq (by push_cast at hc4; linarith)]; simpa using hL4
    · have e4 : j * 3 + 1 = (j - 1) * 3 + 4 := by omega
      rw [e4] at hc4 ⊢
      exact completelyMixable_add A three_ne_zero hm h1 hKm hLm hLK hAK hAL hL0 hKfin hL4
        (by omega) hc4

/-- A real `2 × 2` matrix with `M³ = 1` and the eigenvalue `1` is the identity (its other
eigenvalue is then real with cube `1`, so `1`, and Cayley–Hamilton gives `M³ = 3M - 2`). -/
lemma matrix_two_eq_one {M : Matrix (Fin 2) (Fin 2) ℝ} (h3 : M ^ 3 = 1)
    (hdet : (M - 1).det = 0) : M = 1 := by
  have hδ : M.det ^ 3 = 1 := by rw [← Matrix.det_pow, h3, Matrix.det_one]
  rw [Matrix.det_fin_two] at hδ hdet
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  have hδ1 : a * d - b * c = 1 := by
    have h' : (a * d - b * c - 1) * ((a * d - b * c) ^ 2 + (a * d - b * c) + 1) = 0 := by
      linear_combination hδ
    have : (a * d - b * c) ^ 2 + (a * d - b * c) + 1 ≠ 0 := by
      nlinarith [sq_nonneg (a * d - b * c + 1 / 2)]
    linarith [(mul_eq_zero.1 h').resolve_right this]
  have hd : d = 2 - a := by linarith
  have hbc : b * c = -(a - 1) ^ 2 := by rw [hd] at hδ1; linarith
  have e := fun i j => congrFun (congrFun h3 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10
  have ha : a = 1 := by
    linear_combination (1 / 3) * e00 - (1 / 3) * (a + 2) * hbc - (1 / 3) * b * c * hd
  have hb : b = 0 := by
    linear_combination (1 / 3) * e01 - (1 / 3) * b * hbc - (1 / 3) * b * (2 + d) * hd
  have hc : c = 0 := by
    linear_combination (1 / 3) * e10 - (1 / 3) * c * hbc - (1 / 3) * c * (2 + d) * hd
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simp only [Fin.mk_one, Fin.isValue, Matrix.one_apply_eq]; rw [← show d = M 1 1 from rfl, hd,
      ha]; norm_num

local notation "E" d => EuclideanSpace ℝ (Fin d)

/-- **In the plane every affine bijection `A ≠ id` with `A³ = id` has a linear part without
the eigenvalue `1`.** -/
theorem no_eigen_one_plane (A : (E 2) ≃ᵃ[ℝ] (E 2)) (hm : (⇑A)^[3] = id) (hA : ∃ x, A x ≠ x) :
    ∀ v, A.linear v = v → v = 0 := by
  intro v hv
  by_contra hv0
  set A₀ : (E 2) →ₗ[ℝ] (E 2) := (A.linear : (E 2) →ₗ[ℝ] (E 2))
  set bs := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  set M := LinearMap.toMatrixAlgEquiv bs A₀
  have hM3 : M ^ 3 = 1 := by
    rw [← map_pow, linear_pow_eq_one A hm, map_one]
  have hdet : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨bs.repr v, fun h => hv0 (bs.repr.injective (by
      rw [map_zero]; exact DFunLike.coe_injective h)), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, show M = LinearMap.toMatrix bs bs A₀ by
      ext i j; simp [M, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply],
      LinearMap.toMatrix_mulVec_repr]
    rw [show A₀ v = v from hv, sub_self]
  have hM := matrix_two_eq_one hM3 hdet
  have hA₀ : A₀ = 1 := (LinearMap.toMatrixAlgEquiv bs).injective (by rw [map_one]; exact hM)
  have hx : ∀ x, A x = x + A 0 := fun x => by
    rw [affine_lin A x]; change A₀ x + A 0 = _; rw [hA₀]; rfl
  have h0 : A 0 = 0 := by
    have := congrFun hm 0
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at this
    rw [hx (A 0), hx (A 0 + A 0)] at this
    have h3 : (3 : ℝ) • A 0 = 0 := by
      rw [show (3 : ℝ) • A 0 = A 0 + A 0 + A 0 by module]; exact this
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  obtain ⟨x, hx'⟩ := hA
  exact hx' (by rw [hx, h0, add_zero])

/-- `u₂ = 2^{2/2} 3^{3/2}/(2! |B²|) = 3√3/π`. -/
lemma u_two : (2 : ℝ) ^ ((2 : ℝ) / 2) * (3 : ℝ) ^ ((3 : ℝ) / 2) / (2 * Real.pi) =
    3 * √3 / Real.pi := by
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one,
    show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  field_simp

/-- `2u₂ = 6√3/π < 5` and `4u₂ = 12√3/π < 7`. -/
lemma u_two_bounds : 2 * (3 * √3 / Real.pi) < 5 ∧ 4 * (3 * √3 / Real.pi) < 7 := by
  have h3 : √3 ≤ 1.7321 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hpi := Real.pi_gt_d2
  constructor <;> rw [← mul_div_assoc, div_lt_iff₀ Real.pi_pos] <;> nlinarith

/-- **Corollary 99(d) in the plane**: with `u₂ = 3√3/π` in Ball's theorem, the uniform
distribution on every planar compact convex set with an affine symmetry of order `3` is
`n`-completely mixable for every `n ≥ 3` other than `4`. -/
theorem partD_plane {K : Set (E 2)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (A : (E 2) ≃ᵃ[ℝ] (E 2)) (hm : (⇑A)^[3] = id) (hA : ∃ x, A x ≠ x) (hAK : A '' K = K)
    (hJB : ∃ (e : E 2) (T : (E 2) →ₗ[ℝ] (E 2)), LinearMap.det T ≠ 0 ∧ ell e T ⊆ K ∧
      (volume K).toReal ≤ 3 * √3 / Real.pi * (volume (ell e T)).toReal)
    (hBM : ∀ X Y Z : Set (E 2), IsCompact X → IsCompact Y → IsCompact Z → X.Nonempty →
      Y.Nonempty → Z.Nonempty → min (volume X) (min (volume Y) (volume Z)) ≤
        volume (avg3 X Y Z)) :
    ∀ n : ℕ, 3 ≤ n → n ≠ 4 → CompletelyMixable n (unifSet K) := by
  obtain ⟨h0, h2, h1⟩ := partD hK hconv A hm (no_eigen_one_plane A hm hA) hAK hJB hBM
  obtain ⟨b2, b4⟩ := u_two_bounds
  intro n hn h4
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h
  · obtain ⟨j, rfl⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
    exact h0 j (by omega)
  · refine h1 n h ?_
    have : (7 : ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
    linarith
  · refine h2 n h ?_
    have : (5 : ℝ) ≤ n := by exact_mod_cast (show 5 ≤ n by omega)
    linarith

end PartD

/-! ### Part (b): the cross-polytope with an inscribed double cone as the core -/

section PartB

variable {m : ℕ}

/-- `ℝ^d = ℝ^{d-1} × ℝ` with `m = d - 1`, points `(y, z)`. -/
abbrev W (m : ℕ) := (Fin m → ℝ) × ℝ

instance (m : ℕ) : (volume : Measure (W m)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The Euclidean norm on `ℝ^m`. -/
def eNorm (y : Fin m → ℝ) : ℝ := √(∑ i, y i ^ 2)

/-- The cross-polytope `conv{±e₁, …, ±e_d} = {(y, z) : ∑|yᵢ| + |z| ≤ 1}`. -/
def crossPoly (m : ℕ) : Set (W m) := {p | ∑ i, |p.1 i| + |p.2| ≤ 1}

/-- The cross-polytope `O` of `ℝ^m`. -/
def crossO (m : ℕ) : Set (Fin m → ℝ) := {y | ∑ i, |y i| ≤ 1}

/-- The Euclidean ball `B_ρ` of `ℝ^m`. -/
def ballE (m : ℕ) (ρ : ℝ) : Set (Fin m → ℝ) := {y | eNorm y ≤ ρ}

/-- The double cone over `B_ρ`: `{(y, z) : |z| ≤ 1, y ∈ (1 - |z|) B_ρ}`. -/
def dcone (m : ℕ) (ρ : ℝ) : Set (W m) := {p | |p.2| ≤ 1 ∧ eNorm p.1 ≤ ρ * (1 - |p.2|)}

/-- The volume of the unit ball of `ℝ^m`, as given by `volume_sum_rpow_le` with `p = 2`. -/
def ballC (m : ℕ) : ℝ := (2 * Real.Gamma (1 / 2 + 1)) ^ m / Real.Gamma (m / 2 + 1)

lemma continuous_eNorm : Continuous (eNorm (m := m)) := by
  unfold eNorm; fun_prop

lemma eNorm_smul (t : ℝ) (y : Fin m → ℝ) : eNorm (t • y) = |t| * eNorm y := by
  unfold eNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

/-- **Volumes of cones by sections**: if the section of `X` at height `z` is `(1 - |z|) S`
for `|z| < 1` and empty for `|z| > 1`, then `|X| = I · |S|` with
`I = ∫_{-1}^{1} (1 - |z|)^m dz`. -/
lemma volume_cone {X : Set (W m)} (hX : MeasurableSet X) {S : Set (Fin m → ℝ)}
    (h1 : ∀ z : ℝ, |z| < 1 → (fun y => (y, z)) ⁻¹' X = (1 - |z|) • S)
    (h2 : ∀ z : ℝ, 1 < |z| → (fun y => (y, z)) ⁻¹' X = ∅) :
    volume X = (∫⁻ z in Ioo (-1 : ℝ) 1, ENNReal.ofReal ((1 - |z|) ^ m)) * volume S := by
  rw [show (volume : Measure (W m)) = volume.prod volume from rfl, Measure.prod_apply_symm hX]
  have hne : ∀ a : ℝ, ∀ᵐ z ∂(volume : Measure ℝ), z ≠ a := fun a => by
    rw [ae_iff]; simp
  have hae : (fun z => volume ((fun y => (y, z)) ⁻¹' X)) =ᵐ[volume]
      (Ioo (-1 : ℝ) 1).indicator (fun z => ENNReal.ofReal ((1 - |z|) ^ m) * volume S) := by
    filter_upwards [hne 1, hne (-1)] with z hz1 hz2
    have hz : |z| ≠ 1 := by
      intro h; rcases abs_eq (zero_le_one) |>.1 h with h | h <;> contradiction
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · rw [indicator_of_mem (abs_lt.1 hlt), h1 z hlt, Measure.addHaar_smul,
        Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg (by linarith) _)]
    · rw [indicator_of_notMem (fun h => by linarith [abs_lt.2 h]), h2 z hgt, measure_empty]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioo,
    lintegral_mul_const _ (by fun_prop)]

lemma section_crossPoly {z : ℝ} (hz : |z| < 1) :
    (fun y => (y, z)) ⁻¹' crossPoly m = (1 - |z|) • crossO m := by
  have ht : 0 < 1 - |z| := by linarith
  ext y
  simp only [mem_preimage, crossPoly, crossO, mem_setOf_eq,
    Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_inv, abs_of_pos ht, ← Finset.mul_sum]
  rw [inv_mul_le_iff₀ ht]; constructor <;> intro h <;> linarith

lemma section_dcone {ρ z : ℝ} (hz : |z| < 1) :
    (fun y => (y, z)) ⁻¹' dcone m ρ = (1 - |z|) • ballE m ρ := by
  have ht : 0 < 1 - |z| := by linarith
  ext y
  simp only [mem_preimage, dcone, ballE, mem_setOf_eq,
    Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', eNorm_smul, abs_inv, abs_of_pos ht]
  rw [inv_mul_le_iff₀ ht]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hz.le, by linarith⟩

lemma measurableSet_crossPoly : MeasurableSet (crossPoly m) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

lemma measurableSet_dcone (ρ : ℝ) : MeasurableSet (dcone m ρ) := by
  have e : dcone m ρ = {p : W m | |p.2| ≤ 1} ∩ {p | eNorm p.1 ≤ ρ * (1 - |p.2|)} := rfl
  rw [e]
  exact ((isClosed_le (continuous_abs.comp continuous_snd) continuous_const).inter
    (isClosed_le (continuous_eNorm.comp continuous_fst) (continuous_const.mul
      (continuous_const.sub (continuous_abs.comp continuous_snd))))).measurableSet

lemma volume_crossPoly :
    volume (crossPoly m) =
      (∫⁻ z in Ioo (-1 : ℝ) 1, ENNReal.ofReal ((1 - |z|) ^ m)) * volume (crossO m) :=
  volume_cone measurableSet_crossPoly (fun z hz => section_crossPoly hz) fun z hz => by
    ext y
    simp only [mem_preimage, crossPoly, mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
    have : 0 ≤ ∑ i, |y i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith

lemma volume_dcone (ρ : ℝ) :
    volume (dcone m ρ) =
      (∫⁻ z in Ioo (-1 : ℝ) 1, ENNReal.ofReal ((1 - |z|) ^ m)) * volume (ballE m ρ) :=
  volume_cone (measurableSet_dcone ρ) (fun z hz => section_dcone hz) fun z hz => by
    ext y
    simp only [mem_preimage, dcone, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and,
      not_le]
    intro h; linarith

lemma volume_crossO (hm : 0 < m) :
    volume (crossO m) = ENNReal.ofReal (2 ^ m / m.factorial) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := volume_sum_rpow_le (ι := Fin m) (p := 1) le_rfl 1
  have hs : {x : Fin m → ℝ | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / 1 : ℝ) ≤ 1} = crossO m := by
    ext x; simp [crossO]
  rw [hs] at h
  rw [h, ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  congr 1
  rw [show (1 : ℝ) / 1 + 1 = 2 by norm_num, Real.Gamma_two, div_one,
    Real.Gamma_nat_eq_factorial]
  ring

lemma volume_ballE (hm : 0 < m) (ρ : ℝ) :
    volume (ballE m ρ) = ENNReal.ofReal ρ ^ m * ENNReal.ofReal (ballC m) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := volume_sum_rpow_le (ι := Fin m) (p := 2) one_le_two ρ
  have hs : {x : Fin m → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ ρ} = ballE m ρ := by
    ext x; simp [ballE, eNorm, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]
  rw [hs, Fintype.card_fin] at h
  rw [h, ballC]

lemma two_gamma_three_halves : 2 * Real.Gamma (1 / 2 + 1) = √Real.pi := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring

lemma ballC_pos (m : ℕ) : 0 < ballC m := by
  unfold ballC
  have : 0 < Real.Gamma (1 / 2 + 1) := Real.Gamma_pos_of_pos (by norm_num)
  exact div_pos (pow_pos (by positivity) _) (Real.Gamma_pos_of_pos (by positivity))

/-- `|B³| = 4π/3`. -/
lemma ballC_three : ballC 3 = 4 * Real.pi / 3 := by
  unfold ballC
  rw [two_gamma_three_halves, show ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hs : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hp : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  rw [hs]; ring

/-- `|B⁴| = π²/2`. -/
lemma ballC_four : ballC 4 = Real.pi ^ 2 / 2 := by
  unfold ballC
  rw [two_gamma_three_halves, show ((4 : ℕ) : ℝ) / 2 + 1 = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
  have hs : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [show √Real.pi ^ 4 = (√Real.pi ^ 2) ^ 2 by ring, hs]
  norm_num

/-- `v_m = 2^m m^{m/2}/(m! |B^m|)`. -/
def vcross (m : ℕ) : ℝ := 2 ^ m * √m ^ m / (m.factorial * ballC m)

lemma vcross_three : vcross 3 = 3 * √3 / Real.pi := by
  unfold vcross
  rw [ballC_three]
  have h3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  push_cast
  rw [show √(3 : ℝ) ^ 3 = √3 ^ 2 * √3 by ring, h3]
  field_simp
  norm_num [Nat.factorial]

lemma vcross_four : vcross 4 = 64 / (3 * Real.pi ^ 2) := by
  unfold vcross
  rw [ballC_four]
  push_cast
  rw [show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  field_simp
  norm_num [Nat.factorial]

/-- `243 < 25π²`, so `3v₃ = 9√3/π < 5`. -/
lemma three_vcross_three : 243 < 25 * Real.pi ^ 2 ∧ 3 * vcross 3 < 5 := by
  have hpi := Real.pi_gt_d2
  have h3 : √3 ≤ 1.7321 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  refine ⟨by nlinarith, ?_⟩
  rw [vcross_three, ← mul_div_assoc, div_lt_iff₀ Real.pi_pos]; nlinarith

/-- `64 < 7π²`, so `3v₄ = 64/π² < 7`. -/
lemma three_vcross_four : 64 < 7 * Real.pi ^ 2 ∧ 3 * vcross 4 < 7 := by
  have hpi := Real.pi_gt_d2
  refine ⟨by nlinarith, ?_⟩
  rw [vcross_four, show 3 * (64 / (3 * Real.pi ^ 2)) = 64 / Real.pi ^ 2 by
    field_simp, div_lt_iff₀ (by positivity)]
  nlinarith

lemma pointReflection_zero_of_neg {X : Set (W m)} (h : ∀ p ∈ X, -p ∈ X) :
    AffineEquiv.pointReflection ℝ (0 : W m) '' X = X := by
  have e : ∀ p : W m, AffineEquiv.pointReflection ℝ (0 : W m) p = -p := fun p => by
    rw [pointReflection_apply']; abel
  refine Subset.antisymm (fun _ ⟨p, hp, hpe⟩ => hpe ▸ (e p).symm ▸ h p hp)
    fun p hp => ⟨-p, h p hp, by rw [e, neg_neg]⟩

/-- `∑ |yᵢ| ≤ √m ‖y‖₂` (Cauchy–Schwarz), so `B_ρ ⊆ O` for `ρ = m^{-1/2}`. -/
lemma sum_abs_le (y : Fin m → ℝ) : ∑ i, |y i| ≤ √m * eNorm y := by
  unfold eNorm
  rw [← Real.sqrt_mul (Nat.cast_nonneg m)]
  apply le_sqrt_of (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |y i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sq_abs] at this
  linarith

/-- **Corollary 99(b).** The cross-polytope of `ℝ^{m+1}` with the double cone over the ball of
radius `ρ = m^{-1/2}` as the core. Cited result, as a hypothesis: `hL3` (Theorem 70 with
Theorem 51: `U(L)` is `3`-completely mixable; the paper needs `d = m + 1 ≥ 3`). Then `U(K)` is
`n`-completely mixable for every even `n ≥ 2` and every odd `n ≥ 3 v_m`. -/
theorem partB (hm : 0 < m) (hL3 : CompletelyMixable 3 (unifSet (dcone m (1 / √m)))) :
    (∀ n : ℕ, Even n → n ≠ 0 → CompletelyMixable n (unifSet (crossPoly m))) ∧
      (∀ n : ℕ, Odd n → 3 * vcross m ≤ n → CompletelyMixable n (unifSet (crossPoly m))) := by
  set ρ := 1 / √(m : ℝ)
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hρ : 0 < ρ := by positivity
  set I := ∫⁻ z in Ioo (-1 : ℝ) 1, ENNReal.ofReal ((1 - |z|) ^ m)
  have hI0 : I ≠ 0 := by
    refine (setLIntegral_pos_iff (by fun_prop)).2 ?_ |>.ne'
    have : Function.support (fun z : ℝ => ENNReal.ofReal ((1 - |z|) ^ m)) ∩ Ioo (-1) 1 =
        Ioo (-1) 1 := by
      refine inter_eq_right.2 fun z hz => ?_
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (by linarith [abs_lt.2 hz]) _
    rw [this, Real.volume_Ioo]; norm_num
  have hLK : dcone m ρ ⊆ crossPoly m := by
    intro p ⟨hz, hy⟩
    simp only [crossPoly, mem_setOf_eq]
    have := sum_abs_le p.1
    have h2 : √(m : ℝ) * eNorm p.1 ≤ √m * (ρ * (1 - |p.2|)) :=
      mul_le_mul_of_nonneg_left hy hsm.le
    rw [show √(m : ℝ) * (ρ * (1 - |p.2|)) = 1 - |p.2| by simp only [ρ]; field_simp] at h2
    linarith
  have hKs := pointReflection_zero_of_neg (X := crossPoly m) fun p hp => by
    simpa [crossPoly] using hp
  have hLs := pointReflection_zero_of_neg (X := dcone m ρ) fun p hp => by
    simpa [dcone, eNorm] using hp
  have hball0 : volume (ballE m ρ) ≠ 0 := by
    rw [volume_ballE hm]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hρ))
      (by simpa using ballC_pos m)
  have hL0 : volume (dcone m ρ) ≠ 0 := by rw [volume_dcone]; exact mul_ne_zero hI0 hball0
  have hKfin : volume (crossPoly m) ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : W m)) (r := 1)).ne
      (measure_mono fun p hp => ?_)
    simp only [crossPoly, mem_setOf_eq] at hp
    have hs : 0 ≤ ∑ i, |p.1 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_, ?_⟩
    · rw [Real.norm_eq_abs]
      have := Finset.single_le_sum (f := fun j => |p.1 j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
      linarith [abs_nonneg p.2]
    · rw [Real.norm_eq_abs]; linarith
  obtain ⟨hev, hodd⟩ := completelyMixable_centralSymm measurableSet_crossPoly
    (measurableSet_dcone ρ) hLK hKs hLs hL0 hKfin hL3
  refine ⟨hev, fun n hn hle => hodd n hn ?_⟩
  have hIfin : I ≠ ∞ := by
    intro h
    apply hKfin
    rw [volume_crossPoly]
    change I * _ = ∞
    rw [h, volume_crossO hm]
    exact ENNReal.top_mul (by simp; positivity)
  rw [volume_crossPoly, volume_dcone, ENNReal.toReal_mul, ENNReal.toReal_mul, volume_crossO hm,
    volume_ballE hm, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le,
    ENNReal.toReal_ofReal (ballC_pos m).le, ENNReal.toReal_ofReal (by positivity)]
  have hI := ENNReal.toReal_nonneg (a := I)
  have hB := ballC_pos m
  have key : 3 * (2 ^ m / m.factorial) ≤ (n : ℝ) * (ρ ^ m * ballC m) := by
    have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    have hsmm : 0 < √(m : ℝ) ^ m := pow_pos hsm m
    have e1 : 3 * (2 ^ m / (m.factorial : ℝ)) = 3 * vcross m * (ballC m / √(m : ℝ) ^ m) := by
      unfold vcross; field_simp
    have e2 : (n : ℝ) * (ρ ^ m * ballC m) = n * (ballC m / √(m : ℝ) ^ m) := by
      simp only [ρ, one_div, inv_pow]; field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left key hI]

/-- **Corollary 99(b), `d = 4`**: every even `n ≥ 2` and every odd `n ≥ 5`. -/
theorem partB_four (hL3 : CompletelyMixable 3 (unifSet (dcone 3 (1 / √3)))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet (crossPoly 3)) := by
  obtain ⟨hev, hodd⟩ := partB (m := 3) (by norm_num) (by simpa using hL3)
  intro n hn h3
  rcases Nat.even_or_odd n with he | ho
  · exact hev n he (by omega)
  · refine hodd n ho ?_
    have : (5 : ℝ) ≤ n := by
      obtain ⟨k, rfl⟩ := ho
      exact_mod_cast (show 5 ≤ 2 * k + 1 by omega)
    linarith [three_vcross_three.2]

/-- **Corollary 99(b), `d = 5`**: every even `n ≥ 2` and every odd `n ≥ 7`. -/
theorem partB_five (hL3 : CompletelyMixable 3 (unifSet (dcone 4 (1 / √4)))) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → n ≠ 5 → CompletelyMixable n (unifSet (crossPoly 4)) := by
  obtain ⟨hev, hodd⟩ := partB (m := 4) (by norm_num) (by simpa using hL3)
  intro n hn h3 h5
  rcases Nat.even_or_odd n with he | ho
  · exact hev n he (by omega)
  · refine hodd n ho ?_
    have : (7 : ℝ) ≤ n := by
      obtain ⟨k, rfl⟩ := ho
      exact_mod_cast (show 7 ≤ 2 * k + 1 by omega)
    linarith [three_vcross_four.2]

end PartB

end Mixes.SymmCor
