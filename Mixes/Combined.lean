import Mixes.Bridges
import Mixes.KPlusIncl
import Mixes.Unconditional
import Mixes.Quad
import Mixes.Square
import Mixes.Joint
import Mixes.Bipyr

/-!
# Combined statements of results of the paper (draft 14)

For each of the following results every claim was already proved by existing declarations, but
the paper's statement was not written as one theorem. Here each result is stated as one theorem
(all parts, in the paper's objects) and proved from the existing declarations, with the cited
hypotheses (`Thm27Frustum`, Theorem 51 for balls) discharged.

* `res18`: Lemma 18 (`j:lem:uni`), with the paper's procedure of merging two shortest lengths.
* `res43`: Theorem 43 (`s:thm:cone`).
* `res45`: Corollary 45 (`s:cor:pyramid`).
* `res56`: Theorem 56 (`b:thm:frustum`), for a frustum over a base `F` in a hyperplane
  `{ℓ = 1}` of a finite-dimensional space.
* `res57`: Corollary 57 (`b:cor:tsimplex`), for `Δ^q ⊆ ℝ^k` and its images under affine
  bijections.
* `res58`: Corollary 58 (`b:cor:frustumball`), for `P_q` and `C_q` in the paper's coordinates
  `(y, s)` and their images under affine bijections.
* `res59`: Lemma 59 (`b:lem:join`).
* `res79`: Theorem 79 (`g:thm:class`), including the cones over members of `𝒦⁺`.
* `res86`: Proposition 86 (`st:prop:square`), with the paper's notion of a sliced complete mix
  (`Quad.IsSliced`, as in Proposition 87).

The general tool is the transfer of uniform distributions on scaled translates, joint mixes and
complete mixes along affine bijections between finite-dimensional spaces (`unifScaled_image`,
`jointlyMixable_unifScaled_image_iff`, `completelyMixable_unifSet_image_iff`).
-/

open MeasureTheory Set

noncomputable section

set_option linter.unusedSectionVars false

namespace Mixes.Combined

/-! ### Transfer along affine bijections -/

section Transfer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

/-- A linear bijection maps Lebesgue measure to a positive finite multiple of it. -/
lemma map_volume_equiv (A : E ≃L[ℝ] F) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ (volume : Measure E).map A = c • volume := by
  refine ⟨(Measure.addHaarScalarFactor (volume.map A) volume : ENNReal),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map A) volume]
  ext s hs
  simp

/-- `U(A S) = A_* U(S)` for a linear bijection `A`. -/
lemma unifSet_image_equiv (A : E ≃L[ℝ] F) (S : Set E) :
    unifSet (A '' S) = (unifSet S).map A := by
  obtain ⟨c, hc0, hct, he⟩ := map_volume_equiv A.symm
  have := ConeMix.unifSet_preimage_equiv A.symm.toHomeomorph.toMeasurableEquiv hc0 hct he S
  have e1 : A.symm.toHomeomorph.toMeasurableEquiv ⁻¹' S = A '' S := by
    rw [A.image_eq_preimage_symm]; rfl
  rw [e1] at this
  rw [this]
  rfl

/-- `U(t + r (A K + b)) = A_* U(A⁻¹(t + r b) + r K)`. -/
lemma unifScaled_image (A : E ≃L[ℝ] F) (b : F) (K : Set E) (t : F) (r : ℝ) :
    unifScaled ((fun x => A x + b) '' K) t r =
      (unifScaled K (A.symm (t + r • b)) r).map A := by
  unfold unifScaled
  split_ifs with hr
  · subst hr
    rw [Measure.map_dirac' A.continuous.measurable]
    simp
  · rw [← unifSet_image_equiv, image_image, image_image]
    congr 1
    refine image_congr fun x _ => ?_
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    rw [smul_add]; abel

/-- Joint mixability is preserved by affine maps `x ↦ aᵢ + A x`. -/
lemma jointlyMixable_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] {n : ℕ} {μ : Fin n → Measure E}
    (h : JointlyMixable μ) (A : E →L[ℝ] G) (a : Fin n → G) :
    JointlyMixable fun i => (μ i).map (fun x => a i + A x) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨_, hP.map_affine A.toLinearMap.toAddMonoidHom A.continuous.measurable a⟩

/-- Joint mixability of the scaled translates of an affine image `A K + b` is that of the
corresponding scaled translates of `K`. -/
theorem jointlyMixable_unifScaled_image_iff (A : E ≃L[ℝ] F) (b : F) (K : Set E) {n : ℕ}
    (t : Fin n → F) (lam : Fin n → ℝ) :
    (JointlyMixable fun i => unifScaled ((fun x => A x + b) '' K) (t i) (lam i)) ↔
      JointlyMixable fun i => unifScaled K (A.symm (t i + lam i • b)) (lam i) := by
  simp only [unifScaled_image]
  constructor
  · intro h
    have := jointlyMixable_map h (A.symm : F →L[ℝ] E) (fun _ => 0)
    simp only [zero_add] at this
    convert this using 2 with i
    rw [Measure.map_map (by fun_prop) A.continuous.measurable]
    symm
    convert Measure.map_id
    funext x
    simp
  · intro h
    have := jointlyMixable_map h (A : E →L[ℝ] F) (fun _ => 0)
    simpa using this

/-- `U(s + K) = (s + ·)_* U(K)`. -/
lemma unifSet_translate (s : E) (K : Set E) :
    unifSet ((fun x => s + x) '' K) = (unifSet K).map (fun x => s + x) := by
  have := Mixes.Bipyr.unifSet_map_equiv (MeasurableEquiv.addLeft s)
    (measurePreserving_add_left volume s) K
  exact this.symm

/-- `U(A K + b) = (A · + b)_* U(K)`. -/
lemma unifSet_image_affine (A : E ≃L[ℝ] F) (b : F) (K : Set E) :
    unifSet ((fun x => A x + b) '' K) = (unifSet K).map (fun x => b + A x) := by
  have e : (fun x => A x + b) '' K = A '' ((fun x => A.symm b + x) '' K) := by
    rw [image_image]
    refine image_congr fun x _ => ?_
    simp [add_comm]
  rw [e, unifSet_image_equiv, unifSet_translate, Measure.map_map A.continuous.measurable
    (measurable_const_add _)]
  congr 1
  funext x
  simp

/-- Complete mixability of `U(A K + b)` is that of `U(K)`. -/
theorem completelyMixable_unifSet_image_iff (A : E ≃L[ℝ] F) (b : F) (K : Set E) (n : ℕ) :
    CompletelyMixable n (unifSet ((fun x => A x + b) '' K)) ↔ CompletelyMixable n (unifSet K) := by
  rw [unifSet_image_affine]
  constructor
  · intro h
    have := jointlyMixable_map (μ := fun _ : Fin n => (unifSet K).map (fun x => b + A x)) h
      (A.symm : F →L[ℝ] E) (fun _ => -A.symm b)
    have e : ((unifSet K).map (fun x => b + A x)).map
        (fun x => -A.symm b + (A.symm : F →L[ℝ] E) x) = unifSet K := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have : ((fun x => -A.symm b + (A.symm : F →L[ℝ] E) x) ∘ fun x => b + A x) = id := by
        funext x; simp
      rw [this, Measure.map_id]
    rw [e] at this
    exact this
  · intro h
    exact jointlyMixable_map (μ := fun _ : Fin n => unifSet K) h (A : E →L[ℝ] F) (fun _ => b)

/-- Transfer of a Borel family of joint mixes of scaled translates (as in the scaling property)
along a linear bijection. -/
theorem mixFamily_image (A : E ≃L[ℝ] F) {K : Set E} {n : ℕ} (C : (Fin n → ℝ) → Prop)
    (h : ∃ Φ : (Fin n → ℝ) × (Fin n → E) → (ℕ → ℝ) → (Fin n → E),
      Measurable (Function.uncurry Φ) ∧ ∀ (lam : Fin n → ℝ) (t : Fin n → E), C lam →
        IsJointMix (fun i => unifScaled K (t i) (lam i)) (unifSeq.map (Φ (lam, t)))) :
    ∃ Φ : (Fin n → ℝ) × (Fin n → F) → (ℕ → ℝ) → (Fin n → F),
      Measurable (Function.uncurry Φ) ∧ ∀ (lam : Fin n → ℝ) (t : Fin n → F), C lam →
        IsJointMix (fun i => unifScaled (A '' K) (t i) (lam i)) (unifSeq.map (Φ (lam, t))) := by
  obtain ⟨Φ, hΦ, hmix⟩ := h
  refine ⟨fun p ω i => A (Φ (p.1, fun j => A.symm (p.2 j)) ω i), ?_, fun lam t hC => ?_⟩
  · have h1 : Measurable fun z : ((Fin n → ℝ) × (Fin n → F)) × (ℕ → ℝ) =>
        Φ (z.1.1, fun j => A.symm (z.1.2 j)) z.2 :=
      hΦ.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun j => A.symm.continuous.measurable.comp
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
        |>.prodMk measurable_snd)
    exact measurable_pi_iff.2 fun i =>
      A.continuous.measurable.comp ((measurable_pi_apply i).comp h1)
  · have hP := hmix lam (fun j => A.symm (t j)) hC
    have hQ := hP.map_affine (A : E →L[ℝ] F).toLinearMap.toAddMonoidHom A.continuous.measurable
      (fun _ => 0)
    have hΦl : Measurable (Φ (lam, fun j => A.symm (t j))) := hΦ.comp measurable_prodMk_left
    have e1 : ∀ i, unifScaled (A '' K) (t i) (lam i) =
        (unifScaled K (A.symm (t i)) (lam i)).map (fun x => 0 + (A : E →L[ℝ] F) x) := by
      intro i
      have := unifScaled_image A 0 K (t i) (lam i)
      simp only [add_zero, smul_zero] at this
      rw [show (fun x => A x) '' K = A '' K from rfl] at this
      rw [this]
      congr 1; funext x; simp
    have e2 : (unifSeq.map (Φ (lam, fun j => A.symm (t j)))).map
        (fun x i => 0 + (A : E →L[ℝ] F).toLinearMap.toAddMonoidHom (x i)) =
        unifSeq.map (fun ω i => A (Φ (lam, fun j => A.symm (t j)) ω i)) := by
      have hg : Measurable (fun (x : Fin n → E) (i : Fin n) =>
          (0 : F) + (A : E →L[ℝ] F).toLinearMap.toAddMonoidHom (x i)) :=
        measurable_pi_iff.2 fun i => measurable_const.add
          (A.continuous.measurable.comp (measurable_pi_apply i))
      rw [Measure.map_map hg hΦl]
      congr 1
      funext ω i
      simp
    simp only [e1]
    rw [← e2]
    convert hQ using 3 with i
    rfl

/-- The scaling property passes to images under linear bijections (Lemma 48). -/
theorem scalingPropertySet_image (A : E ≃L[ℝ] F) {K : Set E} {c : ℝ}
    (h : ScalingPropertySet K c) : ScalingPropertySet (A '' K) c := by
  intro n hn
  obtain ⟨Φ, hΦ, hmix⟩ := mixFamily_image A
    (fun lam => (∀ i, 0 ≤ lam i) ∧ (∃ i, lam i ≠ 0) ∧ ∀ k, c * lam k ≤ ∑ i, lam i)
    (by
      obtain ⟨Φ, hΦ, hmix⟩ := h n hn
      exact ⟨Φ, hΦ, fun lam t hC => hmix lam t hC.1 hC.2.1 hC.2.2⟩)
  exact ⟨Φ, hΦ, fun lam t h1 h2 h3 => hmix lam t ⟨h1, h2, h3⟩⟩

lemma image_eq_affine_zero (A : E ≃L[ℝ] F) (K : Set E) :
    A '' K = (fun x => A x + 0) '' K := by simp

end Transfer

/-! ### Theorem 43 and Corollary 45: cones and pyramids -/

section Cone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}

/-- **Theorem 43** (`s:thm:cone`). Let `K = coneSet L B ⊆ V` be the cone over
`F = L⁻¹({1} × B)` (`dim V = k = m + 1`, `ℓ = (L ·).1`, `B` measurable, bounded, of finite
positive volume; every compact convex `F` of dimension `k - 1` in `{ℓ = 1}` is of this form), and
let `F` have the scaling property with constant `m_F`. Let `n ≥ 2`.
(a) If `U(t₁ + λ₁K), …, U(tₙ + λₙK)` (`λ ≥ 0`, not all zero) are jointly mixable, then
`(k + 1) max λ ≤ ∑ λ`.
(b) The construction of the paper (levels from Theorem 27, slices from the scaling property of
`F`) is a Borel function `Φ` of `(λ, t)` and of a sequence of independent uniform variables whose
law is a joint mix of these distributions whenever `(k + 1) max λ ≤ ∑ λ` and
`m_F (k + 1) max λ ≤ k ∑ λ`.
Finally `K` has the scaling property with constant `max (k + 1) (m_F (k + 1) / k)`. -/
theorem res43 (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)} (hB : MeasurableSet B)
    (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤) (hBb : Bornology.IsBounded B) {mF : ℝ}
    (hF : ScalingProperty (sliceUnif L B 1) mF) {n : ℕ} (hn : 2 ≤ n) :
    (∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (JointlyMixable fun i => unifScaled (coneSet L B) (t i) (lam i)) →
      ∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i) ∧
    (∃ Φ : (Fin n → ℝ) × (Fin n → V) → (ℕ → ℝ) → (Fin n → V),
      Measurable (Function.uncurry Φ) ∧
      ∀ (lam : Fin n → ℝ) (t : Fin n → V), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
        (∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i) →
        (∀ j, mF * ((m : ℝ) + 2) * lam j ≤ ((m : ℝ) + 1) * ∑ i, lam i) →
        IsJointMix (fun i => unifScaled (coneSet L B) (t i) (lam i))
          (unifSeq.map (Φ (lam, t)))) ∧
    ScalingPropertySet (coneSet L B)
      (max ((m : ℝ) + 2) (mF * ((m : ℝ) + 2) / ((m : ℝ) + 1))) := by
  have e : ∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) →
      (fun i => unifScaled (coneSet L B) (t i) (lam i)) = fun i => coneUnif L B (t i) (lam i) :=
    fun t lam hlam => funext fun i => (ConeMix.coneUnif_eq_unifScaled L (t i) (hlam i)).symm
  refine ⟨fun t lam hlam _ h j => ?_, ?_, ConeMix.cone_scalingProperty L hB hB0 hBt hBb
    (Theorem27.thm27Frustum_zero m) hF⟩
  · rw [e t lam hlam] at h
    exact cone_jointlyMixable_le L hB hB0 hBt t lam hlam h j
  · obtain ⟨Φ, hΦ, hmix⟩ := ConeMix.cone_sufficiency L hB hB0 hBt hBb
      (Theorem27.thm27Frustum_zero m) hF n hn
    exact ⟨Φ, hΦ, fun lam t hlam hne h1 h2 => by
      rw [e t lam hlam]; exact hmix lam t hlam hne h1 h2⟩

/-- **Corollary 45** (`s:cor:pyramid`). Let `P = conv ({a} ∪ Q) ⊆ V` be a pyramid over a
`(d-1)`-dimensional parallelotope `Q = {o + ∑ c_j u_j : c ∈ [0,1]^{d-1}}` (`u` linearly
independent) with apex `a` outside the affine hull of `Q`, `d = dim V = m' + 2 ≥ 2`. For `n ≥ 2`,
`tᵢ ∈ V` and `λᵢ ≥ 0` not all zero, `U(t₁ + λ₁P), …, U(tₙ + λₙP)` are jointly mixable if and
only if `(d + 1) max λ ≤ ∑ λ`; and for `n ≥ 1`, `U(P)` is `n`-completely mixable if and only if
`n ≥ d + 1`. -/
theorem res45 {m' : ℕ} {o a : V} {u : Fin (m' + 1) → V} (hu : LinearIndependent ℝ u)
    (ha : a ∉ affineSpan ℝ (ConeMix.parallelotope o u)) (hV : Module.finrank ℝ V = m' + 2) :
    (∀ (n : ℕ), 2 ≤ n → ∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) →
      (∃ i, lam i ≠ 0) →
      ((JointlyMixable fun i =>
          unifScaled (convexHull ℝ (insert a (ConeMix.parallelotope o u))) (t i) (lam i)) ↔
        ∀ j, ((m' : ℝ) + 3) * lam j ≤ ∑ i, lam i)) ∧
    ∀ (n : ℕ), 1 ≤ n →
      (CompletelyMixable n (unifSet (convexHull ℝ (insert a (ConeMix.parallelotope o u)))) ↔
        m' + 3 ≤ n) :=
  ⟨fun _ hn t lam hlam hne => ConeMix.pyramid_jointlyMixable_iff (Theorem27.thm27Frustum_zero _)
      hu ha hV hn t lam hlam hne,
    fun _ hn => Theorem27.pyramid_completelyMixable_iff' hu ha hV hn⟩

end Cone

/-! ### Theorem 56: frusta -/

section Frustum

open FrustumMix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}

/-- The frustum `K_q = {s y : q ≤ s ≤ 1, y ∈ F}` over `F = coneBase L B` (in the hyperplane
`{ℓ = 1}`, `ℓ = (L ·).1`); `K_0 = coneSet L B` is the cone. -/
def frustumV (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (q : ℝ) (B : Set (Fin m → ℝ)) : Set V :=
  {x | ∃ s ∈ Icc q 1, ∃ y ∈ coneBase L B, x = s • y}

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma frustumV_zero (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (B : Set (Fin m → ℝ)) :
    frustumV L 0 B = coneSet L B := rfl

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [(volume : Measure V).IsAddHaarMeasure] in
lemma frustumV_eq (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (q : ℝ) (B : Set (Fin m → ℝ)) :
    frustumV L q B = L.symm '' frustumSet q B := by
  ext x
  simp only [frustumV, coneBase, frustumSet, mem_image, mem_Icc, mem_ofPred_eq]
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, y, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨(s, s • b), ⟨hs0, hs1, b, hb, rfl⟩, ?_⟩
    rw [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one]
  · rintro ⟨⟨s, y⟩, ⟨hs0, hs1, b, hb, hy⟩, rfl⟩
    simp only at hs0 hs1 hy
    subst hy
    refine ⟨s, ⟨hs0, hs1⟩, _, ⟨b, hb, rfl⟩, ?_⟩
    rw [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one]

/-- **Theorem 56** (`b:thm:frustum`). Let `F = L⁻¹({1} × B)` (`B` measurable, bounded, of finite
positive volume) have the scaling property with constant `m_F`, let `0 ≤ q < 1`,
`K = K_q = frustumV L q B`, `k = dim V = m + 1`, `μ = μ_{k,q}`, and `n ≥ 2`.
(a) If `U(t₁ + λ₁K), …, U(tₙ + λₙK)` (`λ ≥ 0`, not all zero) are jointly mixable, then
`(1 - q) max λ ≤ (1 - μ) ∑ λ` (14).
(b) The construction of the paper is a Borel function `Φ` of `(λ, t)` and of a sequence of
independent uniform variables whose law is a joint mix of these distributions whenever (14) and
`m_F max λ ≤ μ ∑ λ` (15) hold.
Moreover `K` has the scaling property with constant `max (a_{k,q}, m_F / μ_{k,q})`, which is at
most `max (k + 1, m_F (k + 1) / k)` (for `m_F ≥ 0`), and for `q = 0`, `K` is the cone of
Theorem 43. -/
theorem res56 (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) {B : Set (Fin m → ℝ)} (hB : MeasurableSet B)
    (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤) (hBb : Bornology.IsBounded B) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) {mF : ℝ} (hF : ScalingProperty (sliceUnif L B 1) mF) {n : ℕ}
    (hn : 2 ≤ n) :
    (∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
      (JointlyMixable fun i => unifScaled (frustumV L q B) (t i) (lam i)) →
      ∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) ∧
    (∃ Φ : (Fin n → ℝ) × (Fin n → V) → (ℕ → ℝ) → (Fin n → V),
      Measurable (Function.uncurry Φ) ∧
      ∀ (lam : Fin n → ℝ) (t : Fin n → V), (∀ i, 0 ≤ lam i) → (∃ i, lam i ≠ 0) →
        (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) →
        (∀ j, mF * lam j ≤ muKQ (m + 1) q * ∑ i, lam i) →
        IsJointMix (fun i => unifScaled (frustumV L q B) (t i) (lam i))
          (unifSeq.map (Φ (lam, t)))) ∧
    ScalingPropertySet (frustumV L q B) (max (aKQ (m + 1) q) (mF / muKQ (m + 1) q)) ∧
    (0 ≤ mF → max (aKQ (m + 1) q) (mF / muKQ (m + 1) q) ≤
      max (((m + 1 : ℕ) : ℝ) + 1) (mF * ((m + 1 : ℕ) + 1) / (m + 1 : ℕ))) ∧
    frustumV L 0 B = coneSet L B := by
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hfin : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
  have hBsc : ScalingProperty (unifSet B) mF := (ConeMix.scalingProperty_sliceUnif_iff L).1 hF
  obtain ⟨R, hR⟩ := hBb.subset_closedBall 0
  have hBint := integrable_unifSet_of_subset hB hB0 hBt hR
  have h27 : Thm27Frustum (Module.finrank ℝ (Fin m → ℝ)) q := by
    rw [hfin]; exact Theorem27.thm27Frustum m hq0 hq1
  have hK : frustumV L q B = (fun x => L.symm x + 0) '' frustumSet q B := by
    rw [frustumV_eq, image_eq_affine_zero]
  refine ⟨fun t lam hlam _ h j => ?_, ?_, ?_, fun hm => ?_, rfl⟩
  · rw [hK, jointlyMixable_unifScaled_image_iff] at h
    have := frustum_level_necessity hq0 hq1 hB hB0 hBt _ lam hlam h j
    rwa [hfin] at this
  · rw [frustumV_eq]
    refine mixFamily_image L.symm (fun lam => (∀ i, 0 ≤ lam i) ∧ (∃ i, lam i ≠ 0) ∧
      (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) ∧
      (∀ j, mF * lam j ≤ muKQ (m + 1) q * ∑ i, lam i)) ?_ |>.imp fun Φ hΦ =>
        ⟨hΦ.1, fun lam t h1 h2 h3 h4 => hΦ.2 lam t ⟨h1, h2, h3, h4⟩⟩
    obtain ⟨Φ, hΦ, hmix⟩ := frustum_sufficiency hq0 hq1 hB hB0 hBt hBint h27 hBsc n hn
    exact ⟨Φ, hΦ, fun lam t hC => hmix lam t hC.1 hC.2.1 (by rw [hfin]; exact hC.2.2.1)
      (by rw [hfin]; exact hC.2.2.2)⟩
  · rw [frustumV_eq]
    have := frustum_scalingProperty hq0 hq1 hB hB0 hBt hBint h27 hBsc
    rw [hfin] at this
    exact scalingPropertySet_image L.symm this
  · have := frustum_constant_le (k := m + 1) (by omega) hq0 hq1 hm
    exact this

end Frustum

/-! ### Corollary 57: truncated simplices -/

section TSimplex

open FrustumMix

/-- The truncated simplex `Δ^q = {x ∈ ℝ^k : x ≥ 0, q ≤ x₁ + ⋯ + x_k ≤ 1}`, `k = m + 1`. -/
def tsimplexSet (m : ℕ) (q : ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ q ≤ ∑ i, x i ∧ ∑ i, x i ≤ 1}

/-- The linear bijection `x ↦ (x₁ + ⋯ + x_k, (x₂, …, x_k))` of `ℝ^k` onto `ℝ × ℝ^{k-1}`. -/
def sumLinE (m : ℕ) : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin m → ℝ) where
  toFun x := (∑ i, x i, fun j => x j.succ)
  map_add' x y := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Prod.mk_add_mk]; rfl
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply, Prod.smul_mk]; rfl
  invFun p := Fin.cons (p.1 - ∑ j, p.2 j) p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.sum_univ_succ]; ring
    · simp only [Fin.cons_succ]
  right_inv p := by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_add_cancel]

/-- `sumLinE` as a continuous linear equivalence. -/
def sumLin (m : ℕ) : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ × (Fin m → ℝ) :=
  (sumLinE m).toContinuousLinearEquiv

lemma sumLin_apply (m : ℕ) (x : Fin (m + 1) → ℝ) :
    sumLin m x = (∑ i, x i, fun j => x j.succ) := rfl

lemma mem_tsimplexSet_iff {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (x : Fin (m + 1) → ℝ) :
    x ∈ tsimplexSet m q ↔ sumLin m x ∈ frustumSet q (simplexSet m) := by
  rw [sumLin_apply]
  simp only [tsimplexSet, frustumSet, simplexSet, mem_ofPred_eq]
  have hsplit : ∑ i, x i = x 0 + ∑ j : Fin m, x j.succ := Fin.sum_univ_succ x
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have hS : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
    rcases hS.lt_or_eq with hpos | hzero
    · refine ⟨(∑ i, x i)⁻¹ • fun j => x j.succ, ⟨fun j => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hS) (hx _)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hpos, mul_one]
        linarith [hx 0]
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · have h0 : ∀ i, x i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1 hzero.symm i (Finset.mem_univ i)
      refine ⟨0, ⟨fun _ => le_rfl, by simp⟩, ?_⟩
      funext j
      simp [h0]
  · rintro ⟨h1, h2, b, ⟨hb0, hb1⟩, hy⟩
    have hS : 0 ≤ ∑ i, x i := hq0.trans h1
    refine ⟨fun i => ?_, h1, h2⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have ht : ∑ j : Fin m, x j.succ = (∑ i, x i) * ∑ j, b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact congrFun hy j
      have : x 0 = (∑ i, x i) * (1 - ∑ j, b j) := by rw [mul_sub, mul_one, ← ht]; linarith
      rw [this]
      exact mul_nonneg hS (by linarith)
    · have := congrFun hy j
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact mul_nonneg hS (hb0 j)

lemma tsimplexSet_eq {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) :
    tsimplexSet m q = (sumLin m).symm '' frustumSet q (simplexSet m) := by
  ext x
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage]
  exact mem_tsimplexSet_iff hq0 x

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Corollary 57** (`b:cor:tsimplex`). Let `k = m + 1 ≥ 1`, `0 ≤ q < 1`, and let `K` be the
image `A Δ^q + b` of the truncated simplex `Δ^q ⊆ ℝ^k` under an affine bijection `x ↦ A x + b`
onto a space `V` (for `A = id`, `b = 0` this is `Δ^q` itself). For `n ≥ 2`, `tᵢ ∈ V` and
`λᵢ ≥ 0` not all zero, `U(t₁ + λ₁K), …, U(tₙ + λₙK)` are jointly mixable if and only if
`(1 - q) max λ ≤ (1 - μ_{k,q}) ∑ λ` and `k max λ ≤ μ_{k,q} ∑ λ`. For `n ≥ 1`, `U(K)` is
`n`-completely mixable if and only if `n ≥ k + 1`. -/
theorem res57 {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (A : (Fin (m + 1) → ℝ) ≃L[ℝ] V)
    (b : V) :
    (∀ n : ℕ, 2 ≤ n → ∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) →
      (∃ i, lam i ≠ 0) →
      ((JointlyMixable fun i =>
          unifScaled ((fun x => A x + b) '' tsimplexSet m q) (t i) (lam i)) ↔
        (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m + 1) q) * ∑ i, lam i) ∧
          (∀ j, ((m : ℝ) + 1) * lam j ≤ muKQ (m + 1) q * ∑ i, lam i))) ∧
    ∀ n : ℕ, 1 ≤ n →
      (CompletelyMixable n (unifSet ((fun x => A x + b) '' tsimplexSet m q)) ↔ m + 2 ≤ n) := by
  have : (volume : Measure (ℝ × (Fin m → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set A' : (ℝ × (Fin m → ℝ)) ≃L[ℝ] V := (sumLin m).symm.trans A
  have hK : (fun x => A x + b) '' tsimplexSet m q =
      (fun y => A' y + b) '' frustumSet q (simplexSet m) := by
    rw [tsimplexSet_eq hq0, image_image]
    rfl
  refine ⟨fun n hn t lam hlam hne => ?_, fun n hn => ?_⟩
  · rw [hK, jointlyMixable_unifScaled_image_iff]
    exact tsimplex_jointlyMixable_iff hq0 hq1 (Theorem27.thm27Frustum m hq0 hq1)
      Theorem27.thm27Frustum_zero hn _ lam hlam hne
  · rw [hK, completelyMixable_unifSet_image_iff]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · exact ⟨fun h => tsimplex_completelyMixable_le hq0 hq1 le_rfl h, fun h => by omega⟩
    · exact tsimplex_completelyMixable_iff hq0 hq1 (Theorem27.thm27Frustum m hq0 hq1)
        Theorem27.thm27Frustum_zero h2

end TSimplex

/-! ### Corollary 58: frusta of pyramids over cubes and of circular cones -/

section FrustumBall

open FrustumMix

/-- `P_q = {(y, s) ∈ ℝ^{d-1} × ℝ : q ≤ s ≤ 1, 0 ≤ y_j ≤ s}` (`d - 1 = m`), in the paper's
coordinate order. -/
def PqSet (m : ℕ) (q : ℝ) : Set ((Fin m → ℝ) × ℝ) :=
  {p | q ≤ p.2 ∧ p.2 ≤ 1 ∧ ∀ j, 0 ≤ p.1 j ∧ p.1 j ≤ p.2}

/-- `C_q = {(y, s) ∈ ℝ^{d-1} × ℝ : q ≤ s ≤ 1, |y| ≤ s}` (`d - 1 = m`, Euclidean norm). -/
def CqSet (m : ℕ) (q : ℝ) : Set (EuclideanSpace ℝ (Fin m) × ℝ) :=
  {p | q ≤ p.2 ∧ p.2 ≤ 1 ∧ ‖p.1‖ ≤ p.2}

lemma PqSet_eq {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) :
    PqSet m q = (ContinuousLinearEquiv.prodComm ℝ (Fin m → ℝ) ℝ).symm ''
      frustumSet q (cubeSet m) := by
  ext ⟨y, s⟩
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage]
  simp only [PqSet, frustumSet, cubeSet, mem_ofPred_eq, ContinuousLinearEquiv.prodComm_apply,
    Prod.swap_prod_mk, mem_pi, mem_univ, mem_Icc, forall_const]
  constructor
  · rintro ⟨h1, h2, hy⟩
    refine ⟨h1, h2, ?_⟩
    rcases (hq0.trans h1).lt_or_eq with hpos | hzero
    · refine ⟨s⁻¹ • y, fun j => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact ⟨mul_nonneg (inv_nonneg.2 hpos.le) (hy j).1,
          by rw [inv_mul_le_iff₀ hpos, mul_one]; exact (hy j).2⟩
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · refine ⟨0, fun _ => ⟨le_rfl, zero_le_one⟩, ?_⟩
      funext j
      have := hy j
      simp only [Pi.smul_apply, smul_eq_mul, ← hzero, zero_mul]
      linarith [this.1, this.2]
  · rintro ⟨h1, h2, b, hb, hy⟩
    refine ⟨h1, h2, fun j => ?_⟩
    have hS : 0 ≤ s := hq0.trans h1
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨mul_nonneg hS (hb j).1, by nlinarith [(hb j).1, (hb j).2]⟩

lemma CqSet_eq {m : ℕ} {q : ℝ} (hq0 : 0 ≤ q) :
    CqSet m q = (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin m)) ℝ).symm ''
      frustumSet q (ballSet m) := by
  ext ⟨y, s⟩
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage]
  simp only [CqSet, frustumSet, ballSet, mem_ofPred_eq, ContinuousLinearEquiv.prodComm_apply,
    Prod.swap_prod_mk, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨h1, h2, hy⟩
    refine ⟨h1, h2, ?_⟩
    rcases (hq0.trans h1).lt_or_eq with hpos | hzero
    · refine ⟨s⁻¹ • y, ?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_le_iff₀ hpos, mul_one]
        exact hy
      · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · refine ⟨0, by simp, ?_⟩
      rw [← hzero] at hy
      rw [norm_le_zero_iff.1 hy, ← hzero, zero_smul]
  · rintro ⟨h1, h2, b, hb, hy⟩
    refine ⟨h1, h2, ?_⟩
    have hS : 0 ≤ s := hq0.trans h1
    rw [hy, norm_smul, Real.norm_of_nonneg hS]
    nlinarith [norm_nonneg b]

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasureSpace W] [BorelSpace W] [(volume : Measure W).IsAddHaarMeasure]

/-- **Corollary 58** (`b:cor:frustumball`). Let `d = m' + 2 ≥ 2`, `0 ≤ q < 1`, and let
`K_P = A P_q + b`, `K_C = A' C_q + b'` be images of `P_q` and `C_q` (coordinates `(y, s)`) under
affine bijections (for `A = id`, `b = 0` these are `P_q` and `C_q`); write `μ = μ_{d,q}`.
(1) For `n ≥ 1`, `U(K_P)` and `U(K_C)` are `n`-completely mixable if and only if `n ≥ a_{d,q}`.
(2) For `n ≥ 2`, `tᵢ` and `λᵢ ≥ 0` not all zero, the `U(tᵢ + λᵢ K_P)` are jointly mixable if and
only if `(1 - q) max λ ≤ (1 - μ) ∑ λ` and `2 max λ ≤ μ ∑ λ`.
(3) The `U(tᵢ + λᵢ K_C)` are jointly mixable if these two conditions hold, and only if the first
one and `2 max λ ≤ ∑ λ` hold. -/
theorem res58 {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (A : ((Fin (m' + 1) → ℝ) × ℝ) ≃L[ℝ] V) (b : V)
    (A' : (EuclideanSpace ℝ (Fin (m' + 1)) × ℝ) ≃L[ℝ] W) (b' : W) :
    (∀ n : ℕ, 1 ≤ n →
      (CompletelyMixable n (unifSet ((fun x => A x + b) '' PqSet (m' + 1) q)) ↔
        aKQ (m' + 2) q ≤ n)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (CompletelyMixable n (unifSet ((fun x => A' x + b') '' CqSet (m' + 1) q)) ↔
        aKQ (m' + 2) q ≤ n)) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ (t : Fin n → V) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) →
      (∃ i, lam i ≠ 0) →
      ((JointlyMixable fun i =>
          unifScaled ((fun x => A x + b) '' PqSet (m' + 1) q) (t i) (lam i)) ↔
        (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
          (∀ j, 2 * lam j ≤ muKQ (m' + 2) q * ∑ i, lam i))) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ (t : Fin n → W) (lam : Fin n → ℝ), (∀ i, 0 ≤ lam i) →
      (∃ i, lam i ≠ 0) →
      (((∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
          (∀ j, 2 * lam j ≤ muKQ (m' + 2) q * ∑ i, lam i)) →
        JointlyMixable fun i =>
          unifScaled ((fun x => A' x + b') '' CqSet (m' + 1) q) (t i) (lam i)) ∧
      ((JointlyMixable fun i =>
          unifScaled ((fun x => A' x + b') '' CqSet (m' + 1) q) (t i) (lam i)) →
        (∀ j, (1 - q) * lam j ≤ (1 - muKQ (m' + 2) q) * ∑ i, lam i) ∧
          (∀ j, 2 * lam j ≤ ∑ i, lam i))) := by
  have : (volume : Measure (ℝ × (Fin (m' + 1) → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin (m' + 1)))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set AP : (ℝ × (Fin (m' + 1) → ℝ)) ≃L[ℝ] V :=
    (ContinuousLinearEquiv.prodComm ℝ (Fin (m' + 1) → ℝ) ℝ).symm.trans A
  set AC : (ℝ × EuclideanSpace ℝ (Fin (m' + 1))) ≃L[ℝ] W :=
    (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin (m' + 1))) ℝ).symm.trans A'
  have hKP : (fun x => A x + b) '' PqSet (m' + 1) q =
      (fun y => AP y + b) '' frustumSet q (cubeSet (m' + 1)) := by
    rw [PqSet_eq hq0, image_image]; rfl
  have hKC : (fun x => A' x + b') '' CqSet (m' + 1) q =
      (fun y => AC y + b') '' frustumSet q (ballSet (m' + 1)) := by
    rw [CqSet_eq hq0, image_image]; rfl
  have h27 := Theorem27.thm27Frustum (m' + 1) hq0 hq1
  have hball : ScalingProperty (unifSet (ballSet (m' + 1))) 2 := Ball.ball_scalingProperty _
  have ha2 := two_lt_akq (k := m' + 2) (by omega) hq0 hq1
  -- the cube and the ball as bases
  have hPB := measurableSet_cubeSet (m' + 1)
  have hP0 : volume (cubeSet (m' + 1)) ≠ 0 := by rw [volume_cubeSet]; exact one_ne_zero
  have hPt : volume (cubeSet (m' + 1)) ≠ ⊤ := by rw [volume_cubeSet]; exact ENNReal.one_ne_top
  have hCB : MeasurableSet (ballSet (m' + 1)) := Metric.isClosed_closedBall.measurableSet
  have hC0 : volume (ballSet (m' + 1)) ≠ 0 := (Metric.measure_closedBall_pos _ _ one_pos).ne'
  have hCt : volume (ballSet (m' + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hfP : Module.finrank ℝ (Fin (m' + 1) → ℝ) + 1 = m' + 2 := by
    rw [Module.finrank_fin_fun]
  have hfC : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m' + 1))) + 1 = m' + 2 := by simp
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn t lam hlam hne => ?_,
    fun n hn t lam hlam hne => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hKP, completelyMixable_unifSet_image_iff]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := frustum_completelyMixable_le hq0 hq1 hPB hP0 hPt le_rfl h
        rwa [hfP] at this
      · push_cast at h; linarith
    · exact Unconditional.pyramid_completelyMixable_iff hq0 hq1 h2
  · rw [hKC, completelyMixable_unifSet_image_iff]
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · have := frustum_completelyMixable_le hq0 hq1 hCB hC0 hCt le_rfl h
        rwa [hfC] at this
      · push_cast at h; linarith
    · exact Unconditional.circCone_completelyMixable_iff hq0 hq1 h2
  · rw [hKP, jointlyMixable_unifScaled_image_iff]
    exact pyramid_jointlyMixable_iff hq0 hq1 h27 (ConeMix.scalingProperty_cube _) hn _ lam hlam
      hne
  · rw [hKC, jointlyMixable_unifScaled_image_iff]
    exact circCone_sufficiency hq0 hq1 h27 hball hn _ lam hlam hne h.1 h.2
  · rw [hKC, jointlyMixable_unifScaled_image_iff] at h
    exact circCone_necessity hq0 hq1 _ lam hlam h

end FrustumBall

/-! ### Lemma 59: joins -/

section Join

open ClassK

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure]

/-- The join `J(K₁, K₂)` in the paper's coordinates `((1 - θ) u, θ v, θ)`. -/
def joinSetP (K₁ K₂ : Set G) : Set ((G × G) × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ ∃ u ∈ K₁, ∃ v ∈ K₂, p.1 = ((1 - p.2) • u, p.2 • v)}

omit [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [(volume : Measure G).IsAddHaarMeasure] in
lemma joinSetP_eq (K₁ K₂ : Set G) :
    joinSetP K₁ K₂ = ContinuousLinearEquiv.prodComm ℝ ℝ (G × G) '' joinSet K₁ K₂ := by
  ext ⟨x, θ⟩
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage]
  simp only [joinSetP, joinSet, mem_ofPred_eq, ContinuousLinearEquiv.prodComm_symm,
    ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]

/-- **Lemma 59** (`b:lem:join`). Let `K₁, K₂ ⊆ G` (`a = dim G ≥ 0`; measurable, bounded, of
finite positive volume, e.g. compact convex of dimension `a`) have the scaling property with
constants `m₁, m₂`, and let `m = max(m₁, m₂) ≥ 1`. Then the join
`J(K₁, K₂) = {((1 - θ) u, θ v, θ)}` has the scaling property with constant `2m` (with the
paper's construction, `ClassK.joinMix`). -/
theorem res59 {K₁ K₂ : Set G} (h₁ : Good K₁) (h₂ : Good K₂) {m₁ m₂ : ℝ}
    (hs₁ : ScalingPropertySet K₁ m₁) (hs₂ : ScalingPropertySet K₂ m₂) (hm : 1 ≤ max m₁ m₂) :
    ScalingPropertySet (joinSetP K₁ K₂) (2 * max m₁ m₂) := by
  have := isAddHaar_joinSpace (G := G)
  have : (volume : Measure ((G × G) × ℝ)).IsAddHaarMeasure := by
    have : (volume : Measure (G × G)).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]; infer_instance
    rw [Measure.volume_eq_prod]; infer_instance
  rw [joinSetP_eq]
  exact scalingPropertySet_image _ (join_scalingProperty (thm51Ball 1 le_rfl) h₁ h₂ hs₁ hs₂ hm)

end Join

/-! ### Theorem 79: the class `𝒦⁺` -/

section ClassKPlus

open ScaledB

/-- A member of `𝒦⁺` of dimension `0` is a point mass. -/
lemma kPlus_dim_zero {X : Sp} {μ : Measure X.carrier} {d : ℕ} (h : KPlus X μ d) :
    d = 0 → ∃ x, μ = Measure.dirac x := by
  induction h with
  | point X => exact fun _ => ⟨0, rfl⟩
  | ball j hj => exact fun h => absurd h (by omega)
  | affine h M hM b ih =>
    intro hd
    obtain ⟨x, rfl⟩ := ih hd
    exact ⟨M x + b, Measure.map_dirac' (by fun_prop) _⟩
  | prod h₁ h₂ ih₁ ih₂ =>
    intro hd
    obtain ⟨x, rfl⟩ := ih₁ (by omega)
    obtain ⟨y, rfl⟩ := ih₂ (by omega)
    exact ⟨(x, y), Measure.dirac_prod_dirac⟩
  | hull => exact fun h => absurd h (by omega)

/-- A point mass is `1`-completely mixable. -/
lemma completelyMixable_one_dirac {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
    [MeasurableSingletonClass E] (x : E) : CompletelyMixable 1 (Measure.dirac x) := by
  refine ⟨Measure.dirac fun _ => x, inferInstance, ⟨x, ?_⟩, fun j => ?_⟩
  · rw [ae_dirac_eq]
    simp
  · rw [Measure.map_dirac' (measurable_pi_apply j)]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure]

/-- **Theorem 79** (`g:thm:class`).
(1) `𝒦 ⊂ 𝒦⁺` (`InK d K` gives `KPlus (ℝ^d) U(K) d`).
(2) `𝒦⁺` is closed under joins of any dimensions `k₀, k₁ ≥ 1`.
(3) Every member of `𝒦⁺` of dimension `d` has the scaling property with constant `d + 1` (with
the explicit construction composed of Lemmas 1, 48, 53 and Theorems 27, 51, 73).
(4) Its uniform distribution is `n`-completely mixable for every `n ≥ d + 1` (`n ≥ 1`).
(5) If `K = coneSet L B ⊆ V` is the cone over a member `F = L⁻¹({1} × B)` of `𝒦⁺` (`B ⊆ ℝ^m`
compact convex with nonempty interior, `U(B)` in `𝒦⁺` with dimension `m`; `K` has dimension
`d = m + 1`), then `U(K)` is `n`-completely mixable (`n ≥ 1`) exactly for `n ≥ d + 1`. -/
theorem res79 :
    (∀ (d : ℕ) (K : Set (Fin d → ℝ)), ClassK.InK d K → KPlus (KPlusIncl.spF d) (unifSet K) d) ∧
    (∀ (X : Fin 2 → Sp) (F : (j : Fin 2) → Set (X j).carrier), (∀ j, IsCompact (F j)) →
      (∀ j, Convex ℝ (F j)) → (∀ j, (interior (F j)).Nonempty) →
      (∀ j, KPlus (X j) (unifSet (F j)) (Module.finrank ℝ (X j).carrier)) →
      (∀ j, 1 ≤ Module.finrank ℝ (X j).carrier) →
      KPlus (Sp.hull X) (unifSet (convexHull ℝ (({(0:ℝ)} ×ˢ {y | y 0 ∈ F 0 ∧ y 1 = 0}) ∪
        ({(1:ℝ)} ×ˢ {y | y 0 = 0 ∧ y 1 ∈ F 1}))))
        (1 + ∑ j, Module.finrank ℝ (X j).carrier)) ∧
    (∀ (X : Sp) (μ : Measure X.carrier) (d : ℕ), KPlus X μ d →
      IsProbabilityMeasure μ ∧ ScalingProperty μ (d + 1)) ∧
    (∀ (X : Sp) (μ : Measure X.carrier) (d : ℕ), KPlus X μ d →
      ∀ n : ℕ, 1 ≤ n → d + 1 ≤ n → CompletelyMixable n μ) ∧
    (∀ (m : ℕ) (B : Set (Fin m → ℝ)), IsCompact B → Convex ℝ B → (interior B).Nonempty →
      KPlus (KPlusIncl.spF m) (unifSet B) m → ∀ (L : V ≃L[ℝ] ℝ × (Fin m → ℝ)) (n : ℕ), 1 ≤ n →
      (CompletelyMixable n (unifSet (coneSet L B)) ↔ m + 1 + 1 ≤ n)) := by
  refine ⟨fun d K hK => KPlusIncl.inK_subset_kPlus hK, fun X F hF hFc hFi hK hk =>
    KPlus.join X F hF hFc hFi hK hk, fun X μ d h => Bridges.thm79 h,
    fun X μ d h n hn hdn => ?_, fun m B hBc _ hBi hB L n hn => ?_⟩
  · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
    · obtain ⟨x, rfl⟩ := kPlus_dim_zero h (by omega)
      exact completelyMixable_one_dirac x
    · exact Bridges.thm79_completelyMixable h h2 hdn
  · have hBm : MeasurableSet B := hBc.isClosed.measurableSet
    have hB0 : volume B ≠ 0 := by
      exact (lt_of_lt_of_le (isOpen_interior.measure_pos volume hBi)
        (measure_mono interior_subset)).ne'
    have hBt : volume B ≠ ⊤ := hBc.measure_lt_top.ne
    have hsc : ScalingProperty (unifSet B) ((m : ℝ) + 1) := by
      have := (Bridges.thm79 hB).2
      exact_mod_cast this
    have hF : ScalingProperty (sliceUnif L B 1) ((m : ℝ) + 1) :=
      (ConeMix.scalingProperty_sliceUnif_iff L).2 hsc
    constructor
    · intro h
      have e : scaledTranslate 0 1 (coneSet L B) = coneSet L B := by
        ext x; simp [scaledTranslate]
      rw [← e] at h
      have := cone_completelyMixable_le L hBm hB0 hBt 0 hn h
      omega
    · intro hle
      have hK := (res43 L hBm hB0 hBt hBc.isBounded hF (n := n) (by omega)).2.2
      have hmax : max ((m : ℝ) + 2) (((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 1)) =
          (m : ℝ) + 2 := by
        rw [mul_div_cancel_left₀ _ (by positivity), max_self]
      rw [hmax] at hK
      obtain ⟨Φ, -, hmix⟩ := hK n (by omega)
      have hP := hmix (fun _ => 1) (fun _ => 0) (fun _ => zero_le_one)
        ⟨⟨0, by omega⟩, one_ne_zero⟩ (fun _ => by
          simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          exact_mod_cast hle)
      simp only [ConeMix.unifScaled_zero_one] at hP
      exact ⟨_, hP⟩

end ClassKPlus

/-! ### Proposition 86: the square sliced parallel to a diagonal -/

section Square

open Quad ProbabilityTheory

/-- The square `K = {(t, y) : |t| + |y| ≤ 1}`, in the coordinates (level `t`, position `y`). -/
def squareK : Set (ℝ × ℝ) := {p | |p.1| + |p.2| ≤ 1}

/-- The lower end of the chord of `K` at level `s`. -/
def sqL (s : ℝ) : ℝ := -max (1 - |s|) 0

/-- The upper end of the chord of `K` at level `s`. -/
def sqR (s : ℝ) : ℝ := max (1 - |s|) 0

lemma continuous_sqL : Continuous sqL := by unfold sqL; fun_prop
lemma continuous_sqR : Continuous sqR := by unfold sqR; fun_prop

lemma chord_squareK (s : ℝ) :
    {y | (s, y) ∈ squareK} = if |s| ≤ 1 then Icc (-(1 - |s|)) (1 - |s|) else ∅ := by
  ext y
  simp only [squareK, mem_ofPred_eq]
  split_ifs with h
  · rw [mem_Icc, ← abs_le]; constructor <;> intro h' <;> linarith
  · simp only [mem_empty_iff_false, iff_false, not_le]
    linarith [abs_nonneg y, not_le.1 h]

lemma chordLo_squareK : chordLo squareK = sqL := by
  funext s
  rw [chordLo, chord_squareK, sqL]
  split_ifs with h
  · rw [csInf_Icc (by linarith), max_eq_left (by linarith)]
  · rw [Real.sInf_empty, max_eq_right (by linarith [not_le.1 h]), neg_zero]

lemma chordHi_squareK : chordHi squareK = sqR := by
  funext s
  rw [chordHi, chord_squareK, sqR]
  split_ifs with h
  · rw [csSup_Icc (by linarith), max_eq_left (by linarith)]
  · rw [Real.sSup_empty, max_eq_right (by linarith [not_le.1 h])]

lemma squareK_eq_body : squareK = body (-1) 1 sqL sqR := by
  ext ⟨t, y⟩
  simp only [squareK, body, mem_ofPred_eq, mem_Icc, sqL, sqR]
  constructor
  · intro h
    have ht : |t| ≤ 1 := by linarith [abs_nonneg y]
    rw [max_eq_left (by linarith)]
    have := abs_le.1 ht
    have hy : |y| ≤ 1 - |t| := by linarith
    exact ⟨⟨this.1, this.2⟩, by linarith [(abs_le.1 hy).1], (abs_le.1 hy).2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have ht : |t| ≤ 1 := abs_le.2 ⟨h1, h2⟩
    rw [max_eq_left (by linarith)] at h3 h4
    have : |y| ≤ 1 - |t| := abs_le.2 ⟨by linarith, h4⟩
    linarith

lemma sq_le_R : ∀ s' ∈ Icc (-1 : ℝ) 1, sqL s' ≤ sqR s' := fun s' _ => by
  unfold sqL sqR; linarith [le_max_right (1 - |s'|) 0]

lemma area_square : area (-1) 1 sqL sqR = 2 := by
  rw [area]
  have : ∫ s in Icc (-1 : ℝ) 1, (sqR s - sqL s) = ∫ s in Icc (-1 : ℝ) 1, 2 * (1 - |s|) := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have : |s| ≤ 1 := abs_le.2 hs
    simp only [sqL, sqR, max_eq_left (show 0 ≤ 1 - |s| by linarith)]
    ring
  rw [this, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_const_mul, SquareSlice.integral_density]
  norm_num

/-- The level `t` of a uniform point of the square has the density `1 - |t|` on `[-1, 1]`. -/
theorem map_fst_unifSet_squareK : (unifSet squareK).map Prod.fst = SquareSlice.levelDist := by
  rw [squareK_eq_body, map_fst_unifSet_body continuous_sqL continuous_sqR sq_le_R
    (by rw [area_square]; norm_num), area_square, levelLaw, SquareSlice.levelDist]
  congr 1
  funext s
  rw [SquareSlice.levelDensity, ENNReal.ofReal]
  congr 1
  simp only [sqL, sqR]
  rcases le_total (1 - |s|) 0 with h | h
  · rw [max_eq_right h, Real.toNNReal_of_nonpos h]; simp
  · rw [max_eq_left h]; congr 1; ring

/-- The linear part of the affine bijection `[0,1]² → K`, `(u, v) ↦ (u + v - 1, u - v)`. -/
def sqAE : (Fin 2 → ℝ) ≃ₗ[ℝ] ℝ × ℝ where
  toFun x := (x 0 + x 1, x 0 - x 1)
  map_add' x y := by simp only [Pi.add_apply, Prod.mk_add_mk]; ext <;> simp <;> ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]; ext <;> simp <;> ring
  invFun p := ![(p.1 + p.2) / 2, (p.1 - p.2) / 2]
  left_inv x := by
    funext i; fin_cases i <;> simp
  right_inv p := by ext <;> simp <;> ring

lemma squareK_eq_image :
    squareK = (fun x => sqAE.toContinuousLinearEquiv x + ((-1 : ℝ), (0 : ℝ))) ''
      FrustumMix.cubeSet 2 := by
  ext ⟨t, y⟩
  simp only [squareK, mem_ofPred_eq, mem_image, FrustumMix.cubeSet, mem_pi, mem_univ, mem_Icc,
    forall_const]
  constructor
  · intro h
    have h1 := abs_le.1 (show |t + y| ≤ 1 by linarith [abs_add_le t y])
    have h2 := abs_le.1 (show |t - y| ≤ 1 by linarith [abs_sub t y])
    refine ⟨![(t + 1 + y) / 2, (t + 1 - y) / 2], fun i => ?_, ?_⟩
    · fin_cases i <;> simp <;> constructor <;> linarith
    · show ((t + 1 + y) / 2 + (t + 1 - y) / 2 + -1, (t + 1 + y) / 2 - (t + 1 - y) / 2 + 0) = (t, y)
      ext <;> simp <;> ring
  · rintro ⟨x, hx, hxp⟩
    have hp : ((x 0 + x 1) + -1, (x 0 - x 1) + 0) = (t, y) := hxp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    have h0 := hx 0; have h1 := hx 1
    rcases abs_cases (x 0 + x 1 + -1) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
      rcases abs_cases (x 0 - x 1 + 0) with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      · rw [ha, hb]; linarith [h0.1, h0.2, h1.1, h1.2]

/-- The square is `n`-completely mixable for every `n ≥ 2` (an affine image of `[0,1]²`). -/
theorem squareK_completelyMixable {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet squareK) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [squareK_eq_image, completelyMixable_unifSet_image_iff]
  exact ScaledB.completelyMixable_of_scalingProperty (ConeMix.scalingProperty_cube 2) hn
    (by exact_mod_cast hn)


/-- Null sets of levels forced by the slicing: if almost surely the `i`-th position avoids `Bz`
when the levels lie in `A`, while every chord at a level in `A` gives `Bz` probability at least
`ε > 0`, then the levels lie in `A` with probability `0`. -/
lemma sliced_null {P : Measure (Fin 3 → ℝ × ℝ)} [IsProbabilityMeasure P] (hsl : IsSliced sqL sqR P) (i : Fin 3)
    {A : Set (Fin 3 → ℝ)} (hA : MeasurableSet A) {Bz : Set ℝ} (hBz : MeasurableSet Bz) {ε : ℝ}
    (hε : 0 < ε) (h1 : ∀ᵐ x ∂P, ¬ (lev3 x ∈ A ∧ (x i).2 ∈ Bz))
    (h2 : ∀ s ∈ A, ENNReal.ofReal ε ≤
      unit01 {t | sqL (s i) + t * (sqR (s i) - sqL (s i)) ∈ Bz}) :
    P.map lev3 A = 0 := by
  have hT : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Bz} := measurable_snd hBz
  have hG : Measurable fun x : Fin 3 → ℝ × ℝ => (lev3 x, x i) :=
    measurable_lev3.prodMk (measurable_pi_apply i)
  have e0 : P.map (fun x => (lev3 x, x i)) (A ×ˢ {z : ℝ × ℝ | z.2 ∈ Bz}) = 0 := by
    rw [Measure.map_apply hG (hA.prod hT)]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [h1] with x hx hmem
    exact hx ⟨hmem.1, hmem.2⟩
  have : IsSFiniteKernel (chordKernel sqL sqR) := by unfold chordKernel; infer_instance
  have : IsProbabilityMeasure (P.map lev3) := inferInstance
  rw [hsl i, Measure.compProd_apply_prod hA hT] at e0
  have hle : ∫⁻ _ in A, ENNReal.ofReal ε ∂(P.map lev3) ≤
      ∫⁻ s in A, ((chordKernel sqL sqR).comap (fun s : Fin 3 → ℝ => s i)
        (measurable_pi_apply i)) s {z : ℝ × ℝ | z.2 ∈ Bz} ∂(P.map lev3) := by
    refine setLIntegral_mono' hA fun s hs => ?_
    rw [Kernel.comap_apply, chordKernel_apply continuous_sqL continuous_sqR,
      Measure.map_apply (by fun_prop) hT]
    exact h2 s hs
  rw [e0, setLIntegral_const, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h | h
  · exact absurd h (ENNReal.ofReal_pos.2 hε).ne'
  · exact h

lemma unit01_Ico {δ : ℝ} (hδ1 : δ ≤ 1) : unit01 (Ico 0 δ) = ENNReal.ofReal δ := by
  rw [unit01, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.2 (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hδ1)), Real.volume_Ico,
    sub_zero]

lemma unit01_Ioc {δ : ℝ} (hδ1 : δ ≤ 1) :
    unit01 (Ioc (1 - δ) 1) = ENNReal.ofReal δ := by
  rw [unit01, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl)),
    Real.volume_Ioc]
  congr 1; ring

/-- **Proposition 86**, the slicing part: the uniform distribution on the square
`K = {(t, y) : |t| + |y| ≤ 1}` has no `3`-complete mix that is sliced parallel to the diagonal
`t = 0` (with the level `t`), in the sense of `Quad.IsSliced` (given the levels of its points,
each point is uniformly distributed on its chord). -/
theorem no_sliced_square : ¬ ∃ P : Measure (Fin 3 → ℝ × ℝ),
    IsCompleteMix 3 (unifSet squareK) P ∧ IsSliced (chordLo squareK) (chordHi squareK) P := by
  rintro ⟨P, hP, hsl⟩
  rw [chordLo_squareK, chordHi_squareK] at hsl
  obtain ⟨hPp, ⟨s₀, hsum⟩, hmarg⟩ := hP
  set Q := P.map lev3 with hQdef
  have hKm : MeasurableSet squareK := measurableSet_le (by fun_prop) measurable_const
  have hm : ∀ j : Fin 3, P.map (fun x => x j) = unifSet squareK := fun j => hmarg j
  have hmem : ∀ j : Fin 3, ∀ᵐ x ∂P, x j ∈ squareK := fun j =>
    ae_of_ae_map (measurable_pi_apply j).aemeasurable
      (by rw [hm j]; exact FrustumMix.unifSet_ae_mem hKm)
  have hQm : ∀ j : Fin 3, Q.map (fun s => s j) = SquareSlice.levelDist := by
    intro j
    rw [hQdef, Measure.map_map (measurable_pi_apply j) measurable_lev3,
      ← map_fst_unifSet_squareK, ← hm j, Measure.map_map measurable_fst (measurable_pi_apply j)]
    rfl
  have hQ : IsCompleteMix 3 SquareSlice.levelDist Q := by
    refine ⟨inferInstance, ⟨s₀.1, ?_⟩, hQm⟩
    rw [hQdef, ae_map_iff measurable_lev3.aemeasurable
      (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [hsum] with x hx
    simp only [lev3]
    rw [← hx, Prod.fst_sum]
  apply SquareSlice.no_polygon_complete_mix Q hQ
  have hcube : ∀ᵐ s ∂Q, ∀ j, |s j| ≤ 1 := ae_all_iff.2 fun j =>
    ae_of_ae_map (measurable_pi_apply j).aemeasurable (by
      rw [hQm j]
      filter_upwards [SquareSlice.levelDist_ae_mem] with t ht
      exact abs_le.2 ht)
  have hpos : ∀ᵐ x ∂P, ∀ j, |(x j).2| ≤ 1 - |(x j).1| := ae_all_iff.2 fun j =>
    (hmem j).mono fun x hx => by
      simp only [squareK, mem_ofPred_eq] at hx; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = s₀.2 := ⟨_, rfl⟩
  have hsum2 : ∀ᵐ x ∂P, ∑ j, (x j).2 = c := hsum.mono fun x hx => by
    rw [hc, ← hx, Prod.snd_sum]
  have hcm : MeasurableSet {s : Fin 3 → ℝ | ∀ j, |s j| ≤ 1} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  -- the bound on one position from the others
  have hbound : ∀ i : Fin 3, ∀ᵐ x ∂P,
      |(x i).2 - c| ≤ ∑ j ∈ Finset.univ.erase i, (1 - |(x j).1|) := by
    intro i
    filter_upwards [hpos, hsum2] with x hp hs2
    have e := Finset.add_sum_erase Finset.univ (fun j => (x j).2) (Finset.mem_univ i)
    have : (x i).2 - c = -∑ j ∈ Finset.univ.erase i, (x j).2 := by linarith
    rw [this, abs_neg]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hp j)
  have key : ∀ i : Fin 3, ∀ᵐ s ∂Q, (∀ j, |s j| ≤ 1) →
      1 - |s i| ≤ ∑ j ∈ Finset.univ.erase i, (1 - |s j|) := by
    intro i
    set N := {s : Fin 3 → ℝ | (∀ j, |s j| ≤ 1) ∧
      ∑ j ∈ Finset.univ.erase i, (1 - |s j|) < 1 - |s i|}
    suffices hN : Q N = 0 by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with s hs hc
      exact not_lt.1 fun h => hs ⟨hc, h⟩
    rcases le_or_gt 0 c with hc | hc
    · -- positions bounded below by `-∑_{j ≠ i} r(S_j)`
      set A : ℚ → ℕ → Set (Fin 3 → ℝ) := fun q k => {s | (∀ j, |s j| ≤ 1) ∧
        -(1 - |s i|) + 1 / ((k : ℝ) + 1) ≤ q ∧ (q : ℝ) < -∑ j ∈ Finset.univ.erase i, (1 - |s j|)}
      have hNA : N ⊆ ⋃ (q : ℚ) (k : ℕ), A q k := by
        rintro s ⟨hs, hlt⟩
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show -(1 - |s i|) <
          -∑ j ∈ Finset.univ.erase i, (1 - |s j|) by linarith)
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < q + (1 - |s i|) by linarith)
        exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨k, hs, by linarith, hq2⟩⟩
      refine measure_mono_null hNA (measure_iUnion_null fun q => measure_iUnion_null fun k => ?_)
      have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hδ1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hδ2 : 1 / ((k : ℝ) + 1) / 2 ≤ 1 := by linarith
      have hAm : MeasurableSet (A q k) := by
        show MeasurableSet ({s : Fin 3 → ℝ | ∀ j, |s j| ≤ 1} ∩
          ({s | -(1 - |s i|) + 1 / ((k : ℝ) + 1) ≤ q} ∩
            {s | (q : ℝ) < -∑ j ∈ Finset.univ.erase i, (1 - |s j|)}))
        exact hcm.inter ((measurableSet_le (by fun_prop) measurable_const).inter
          (measurableSet_lt measurable_const
            (by fun_prop : Measurable fun s : Fin 3 → ℝ =>
              -∑ j ∈ Finset.univ.erase i, (1 - |s j|))))
      refine sliced_null hsl i hAm (measurableSet_Iio (a := (q : ℝ))) (half_pos hδ) ?_ ?_
      · filter_upwards [hbound i] with x hx ⟨⟨_, _, hlt⟩, hy⟩
        simp only [lev3, mem_Iio] at hlt hy
        have := (abs_le.1 hx).1
        linarith
      · rintro s ⟨hs, hq, -⟩
        have hr0 : 0 ≤ 1 - |s i| := by linarith [hs i]
        have hr1 : 1 - |s i| ≤ 1 := by linarith [abs_nonneg (s i)]
        rw [← unit01_Ico hδ2]
        refine measure_mono fun t ht => ?_
        simp only [mem_Ico] at ht
        simp only [sqL, sqR, max_eq_left hr0, mem_ofPred_eq, mem_Iio]
        nlinarith [mul_le_mul_of_nonneg_left hr1 ht.1]
    · -- positions bounded above by `∑_{j ≠ i} r(S_j)`
      set A : ℚ → ℕ → Set (Fin 3 → ℝ) := fun q k => {s | (∀ j, |s j| ≤ 1) ∧
        (q : ℝ) + 1 / ((k : ℝ) + 1) ≤ 1 - |s i| ∧ ∑ j ∈ Finset.univ.erase i, (1 - |s j|) < q}
      have hNA : N ⊆ ⋃ (q : ℚ) (k : ℕ), A q k := by
        rintro s ⟨hs, hlt⟩
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (1 - |s i|) - q by linarith)
        exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨k, hs, by linarith, hq1⟩⟩
      refine measure_mono_null hNA (measure_iUnion_null fun q => measure_iUnion_null fun k => ?_)
      have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hδ1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hδ2 : 1 / ((k : ℝ) + 1) / 2 ≤ 1 := by linarith
      have hAm : MeasurableSet (A q k) := by
        show MeasurableSet ({s : Fin 3 → ℝ | ∀ j, |s j| ≤ 1} ∩
          ({s | (q : ℝ) + 1 / ((k : ℝ) + 1) ≤ 1 - |s i|} ∩
            {s | ∑ j ∈ Finset.univ.erase i, (1 - |s j|) < q}))
        exact hcm.inter ((measurableSet_le measurable_const (by fun_prop)).inter
          (measurableSet_lt (by fun_prop : Measurable fun s : Fin 3 → ℝ =>
              ∑ j ∈ Finset.univ.erase i, (1 - |s j|)) measurable_const))
      refine sliced_null hsl i hAm (measurableSet_Ioi (a := (q : ℝ))) (half_pos hδ) ?_ ?_
      · filter_upwards [hbound i] with x hx ⟨⟨_, _, hlt⟩, hy⟩
        simp only [lev3, mem_Ioi] at hlt hy
        have := (abs_le.1 hx).2
        linarith
      · rintro s ⟨hs, hq, hlt⟩
        have hr0 : 0 ≤ 1 - |s i| := by linarith [hs i]
        have hR0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, (1 - |s j|) :=
          Finset.sum_nonneg fun j _ => by linarith [hs j]
        rw [← unit01_Ioc hδ2]
        refine measure_mono fun t ht => ?_
        simp only [mem_Ioc] at ht
        simp only [sqL, sqR, max_eq_left hr0, mem_ofPred_eq, mem_Ioi]
        have hrpos : 0 < 1 - |s i| := by linarith
        have : (1 - 1 / ((k : ℝ) + 1) / 2) * (1 - |s i|) < t * (1 - |s i|) :=
          mul_lt_mul_of_pos_right ht.1 hrpos
        have hr1 : 1 - |s i| ≤ 1 := by linarith [abs_nonneg (s i)]
        nlinarith
  filter_upwards [hcube, ae_all_iff.2 key] with s hs hk i
  have h := hk i hs
  have e := Finset.add_sum_erase Finset.univ (fun j => SquareSlice.r (s j)) (Finset.mem_univ i)
  simp only [SquareSlice.r] at e ⊢
  linarith

/-- **Proposition 86** (`st:prop:square`). Let `K = {(t, y) : |t| + |y| ≤ 1}`, sliced parallel to
a diagonal with the level `t`.
(1) The levels of `U(K)` have the density `1 - |t|` on `[-1, 1]`.
(2) No `3`-complete mix `(T₁, T₂, T₃)` of the levels satisfies the polygon inequality for the
half-lengths `r(t) = 1 - |t|` (almost surely).
(3) Hence `U(K)` has no sliced `3`-complete mix in this direction.
(4) `U(K)` is `n`-completely mixable for every `n ≥ 2`. -/
theorem res86 :
    (unifSet squareK).map Prod.fst = SquareSlice.levelDist ∧
    (¬ ∃ Q : Measure (Fin 3 → ℝ), IsCompleteMix 3 SquareSlice.levelDist Q ∧
      ∀ᵐ x ∂Q, SquareSlice.PolygonIneq x) ∧
    (¬ ∃ P : Measure (Fin 3 → ℝ × ℝ),
      IsCompleteMix 3 (unifSet squareK) P ∧ IsSliced (chordLo squareK) (chordHi squareK) P) ∧
    ∀ n : ℕ, 2 ≤ n → CompletelyMixable n (unifSet squareK) :=
  ⟨map_fst_unifSet_squareK, SquareSlice.no_sliced_mix, no_sliced_square,
    fun _ hn => squareK_completelyMixable hn⟩

end Square

/-! ### Lemma 18: the merging procedure -/

section Lemma18

variable {k : ℕ}

/-- The total length `∑_{j ∈ G} ℓ_j` of a group `G` of coordinates. -/
def glen (ℓ : Fin k → ℝ) (G : Finset (Fin k)) : ℝ := ∑ j ∈ G, ℓ j

/-- The initial state of the procedure of Lemma 18: one group `{j}` for every positive length
(the coordinates with `ℓ_j = 0` are set to `0` and take no further part). -/
def initGroups (ℓ : Fin k → ℝ) : Finset (Finset (Fin k)) :=
  (Finset.univ.filter fun j => 0 < ℓ j).image fun j => {j}

/-- One step of the procedure of Lemma 18: while more than three positive lengths remain, two
shortest of them, the lengths of the groups `G` and `H`, are replaced by the length of the new
coordinate `W` of the merged group `G ∪ H`. -/
def MergeStep (ℓ : Fin k → ℝ) (S S' : Finset (Finset (Fin k))) : Prop :=
  3 < S.card ∧ ∃ G ∈ S, ∃ H ∈ S, G ≠ H ∧ (∀ C ∈ S, glen ℓ G ≤ glen ℓ C) ∧
    (∀ C ∈ S, C ≠ G → glen ℓ H ≤ glen ℓ C) ∧ S' = insert (G ∪ H) ((S.erase G).erase H)

/-- The substitutions of Lemma 18 composed: if the final groups are `G 0, G 1, G 2` with new
coordinates `W_a`, the merging steps give `X_j = ℓ_j W_a / glen (G a)` for `j ∈ G a` (each step
`X_i = ℓ_i W/(ℓ_i + ℓ_j)` multiplies the factors), and `X_j = 0` outside the groups. This is the
image of a point `R = (W₀, W₁, W₂)`. -/
def liftPt (ℓ : Fin k → ℝ) (G : Fin 3 → Finset (Fin k)) (R : Fin 3 → ℝ) : Fin k → ℝ :=
  fun j => ∑ a, if j ∈ G a then ℓ j / glen ℓ (G a) * R a else 0

/-- The invariant of the procedure. -/
structure MInv (ℓ : Fin k → ℝ) (s : ℝ) (S : Finset (Finset (Fin k))) : Prop where
  pos : ∀ G ∈ S, 0 < glen ℓ G
  le : ∀ G ∈ S, glen ℓ G ≤ s
  disj : ∀ G ∈ S, ∀ H ∈ S, G ≠ H → Disjoint G H
  sum : ∑ G ∈ S, glen ℓ G = 2 * s
  cover : ∀ j, 0 < ℓ j → ∃ G ∈ S, j ∈ G
  card : 3 ≤ S.card

lemma minv_init {ℓ : Fin k → ℝ} (hℓ : ∀ j, 0 ≤ ℓ j) {s : ℝ} (hsum : ∑ j, ℓ j = 2 * s)
    (hmax : ∀ j, ℓ j ≤ s) (h3 : 2 < (initGroups ℓ).card) : MInv ℓ s (initGroups ℓ) := by
  have hmem : ∀ G, G ∈ initGroups ℓ ↔ ∃ j, 0 < ℓ j ∧ G = {j} := fun G => by
    simp only [initGroups, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩⟩
  refine ⟨fun G hG => ?_, fun G hG => ?_, fun G hG H hH hGH => ?_, ?_, fun j hj => ?_, by omega⟩
  · obtain ⟨j, hj, rfl⟩ := (hmem G).1 hG
    simpa [glen] using hj
  · obtain ⟨j, hj, rfl⟩ := (hmem G).1 hG
    simpa [glen] using hmax j
  · obtain ⟨i, -, rfl⟩ := (hmem G).1 hG
    obtain ⟨j, -, rfl⟩ := (hmem H).1 hH
    exact Finset.disjoint_singleton.2 fun h => hGH (by rw [h])
  · rw [initGroups, Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
    simp only [glen, Finset.sum_singleton]
    rw [Finset.sum_filter_of_ne (fun j _ hj => lt_of_le_of_ne (hℓ j) (Ne.symm hj)), hsum]
  · exact ⟨{j}, (hmem _).2 ⟨j, hj, rfl⟩, Finset.mem_singleton_self j⟩

lemma minv_step {ℓ : Fin k → ℝ} {s : ℝ} {S S' : Finset (Finset (Fin k))} (h : MInv ℓ s S)
    (hst : MergeStep ℓ S S') : MInv ℓ s S' ∧ S'.card < S.card := by
  obtain ⟨hc, G, hG, H, hH, hGH, hmin1, hmin2, rfl⟩ := hst
  set R := (S.erase G).erase H with hRdef
  have hHR : H ∈ S.erase G := Finset.mem_erase.2 ⟨hGH.symm, hH⟩
  have hRcard : R.card = S.card - 2 := by
    rw [hRdef, Finset.card_erase_of_mem hHR, Finset.card_erase_of_mem hG]; omega
  have hmemR : ∀ C, C ∈ R ↔ C ≠ H ∧ C ≠ G ∧ C ∈ S := fun C => by
    simp only [hRdef, Finset.mem_erase]
  have hdisjGH : Disjoint G H := h.disj G hG H hH hGH
  have hGne : G.Nonempty := by
    rw [← Finset.ne_empty_iff_nonempty]
    rintro rfl
    have := h.pos _ hG
    simp [glen] at this
  have hnot : G ∪ H ∉ R := by
    intro hm
    obtain ⟨-, hmG, hmS⟩ := (hmemR _).1 hm
    have := h.disj _ hmS G hG hmG
    obtain ⟨x, hx⟩ := hGne
    exact Finset.disjoint_left.1 this (Finset.mem_union_left _ hx) hx
  have hglenU : glen ℓ (G ∪ H) = glen ℓ G + glen ℓ H := Finset.sum_union hdisjGH
  have hsumS : ∑ C ∈ S, glen ℓ C = glen ℓ G + glen ℓ H + ∑ C ∈ R, glen ℓ C := by
    rw [← Finset.add_sum_erase S _ hG, ← Finset.add_sum_erase (S.erase G) _ hHR]; ring
  have hcard' : (insert (G ∪ H) R).card = S.card - 1 := by
    rw [Finset.card_insert_of_notMem hnot, hRcard]; omega
  have hUle : glen ℓ (G ∪ H) ≤ s := by
    obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.1 (show 1 < R.card by omega)
    obtain ⟨hCH, hCG, hCS⟩ := (hmemR C).1 hC
    obtain ⟨hDH, hDG, hDS⟩ := (hmemR D).1 hD
    have h1 := hmin1 C hCS; have h2 := hmin1 D hDS
    have h3 := hmin2 C hCS hCG; have h4 := hmin2 D hDS hDG
    have hCD' : glen ℓ C + glen ℓ D ≤ ∑ C ∈ R, glen ℓ C := by
      rw [← Finset.sum_pair hCD]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.insert_subset hC (Finset.singleton_subset_iff.2 hD))
        fun E hE _ => (h.pos E ((hmemR E).1 hE).2.2).le
    have := h.sum
    rw [hglenU]
    linarith
  refine ⟨⟨fun C hC => ?_, fun C hC => ?_, fun C hC D hD hCD => ?_, ?_, fun j hj => ?_, ?_⟩,
    by omega⟩
  · rcases Finset.mem_insert.1 hC with rfl | hC
    · rw [hglenU]; linarith [h.pos G hG, h.pos H hH]
    · exact h.pos C ((hmemR C).1 hC).2.2
  · rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hUle
    · exact h.le C ((hmemR C).1 hC).2.2
  · have key : ∀ E ∈ R, Disjoint (G ∪ H) E := fun E hE => by
      obtain ⟨hEH, hEG, hES⟩ := (hmemR E).1 hE
      exact Finset.disjoint_union_left.2 ⟨h.disj G hG E hES (Ne.symm hEG),
        h.disj H hH E hES (Ne.symm hEH)⟩
    rcases Finset.mem_insert.1 hC with rfl | hC' <;> rcases Finset.mem_insert.1 hD with rfl | hD'
    · exact absurd rfl hCD
    · exact key D hD'
    · exact (key C hC').symm
    · exact h.disj C ((hmemR C).1 hC').2.2 D ((hmemR D).1 hD').2.2 hCD
  · rw [Finset.sum_insert hnot, hglenU, ← h.sum, hsumS]
  · obtain ⟨C, hC, hjC⟩ := h.cover j hj
    by_cases hCG : C = G
    · exact ⟨G ∪ H, Finset.mem_insert_self _ _, Finset.mem_union_left _ (hCG ▸ hjC)⟩
    by_cases hCH : C = H
    · exact ⟨G ∪ H, Finset.mem_insert_self _ _, Finset.mem_union_right _ (hCH ▸ hjC)⟩
    exact ⟨C, Finset.mem_insert_of_mem ((hmemR C).2 ⟨hCH, hCG, hC⟩), hjC⟩
  · omega

lemma minv_reach {ℓ : Fin k → ℝ} {s : ℝ} {S₀ S : Finset (Finset (Fin k))} (h₀ : MInv ℓ s S₀)
    (hr : Relation.ReflTransGen (MergeStep ℓ) S₀ S) : MInv ℓ s S := by
  induction hr with
  | refl => exact h₀
  | tail _ hst ih => exact (minv_step ih hst).1

lemma exists_terminal {ℓ : Fin k → ℝ} {s : ℝ} :
    ∀ (N : ℕ) (S : Finset (Finset (Fin k))), S.card = N → MInv ℓ s S →
      ∃ T, Relation.ReflTransGen (MergeStep ℓ) S T ∧ T.card = 3 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hN h
    by_cases h3 : S.card = 3
    · exact ⟨S, Relation.ReflTransGen.refl, h3⟩
    have hc : 3 < S.card := by have := h.card; omega
    obtain ⟨G, hG, hGmin⟩ := Finset.exists_min_image S (glen ℓ)
      (Finset.card_pos.1 (by omega))
    obtain ⟨H, hH, hHmin⟩ := Finset.exists_min_image (S.erase G) (glen ℓ)
      (Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hG]; omega))
    have hst : MergeStep ℓ S (insert (G ∪ H) ((S.erase G).erase H)) :=
      ⟨hc, G, hG, H, Finset.mem_of_mem_erase hH, (Finset.ne_of_mem_erase hH).symm, hGmin,
        fun C hC hCG => hHmin C (Finset.mem_erase.2 ⟨hCG, hC⟩), rfl⟩
    obtain ⟨h', hlt⟩ := minv_step h hst
    obtain ⟨T, hT, hT3⟩ := ih _ (hN ▸ hlt) _ rfl h'
    exact ⟨T, Relation.ReflTransGen.head hst hT, hT3⟩

/-- The final step of Lemma 18: Lemma 17 for the three final groups, lifted to the coordinates. -/
lemma final_mix {ℓ : Fin k → ℝ} (hℓ : ∀ j, 0 ≤ ℓ j) {s : ℝ} {S : Finset (Finset (Fin k))}
    (h : MInv ℓ s S) (hS3 : S.card ≤ 3) (G : Fin 3 → Finset (Fin k)) (hGi : Function.Injective G)
    (hGS : ∀ a, G a ∈ S) :
    let t : Fin 3 → ℝ := fun a => s - glen ℓ (G a)
    IsJointMix (fun j => unifI 0 (ℓ j))
        (segMix (L17.w17 (t 0) (t 1) (t 2)) (fun e => liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e))
          (fun e => liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e))) ∧
      (∀ e, ∑ j, liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e) j = s) ∧
      (∀ e, ∑ j, liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e) j = s) ∧
      ∀ᵐ x ∂segMix (L17.w17 (t 0) (t 1) (t 2))
          (fun e => liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e))
          (fun e => liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e)), ∑ j, x j = s := by
  intro t
  set c : Fin 3 → ℝ := fun a => glen ℓ (G a) with hcdef
  have himg : Finset.univ.image G = S := by
    refine Finset.eq_of_subset_of_card_le (fun C hC => ?_) ?_
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hC; exact hGS a
    · rw [Finset.card_image_of_injective _ hGi, Finset.card_univ, Fintype.card_fin]; exact hS3
  have hcpos : ∀ a, 0 < c a := fun a => h.pos _ (hGS a)
  have hcle : ∀ a, c a ≤ s := fun a => h.le _ (hGS a)
  have hcsum : c 0 + c 1 + c 2 = 2 * s := by
    rw [← h.sum, ← himg, Finset.sum_image (fun a _ b _ hab => hGi hab), Fin.sum_univ_three]
  have hs' : (c 0 + c 1 + c 2) / 2 = s := by linarith
  -- the coordinate formula
  have hcoord : ∀ j, ∃ a₀, ∀ R : Fin 3 → ℝ, liftPt ℓ G R j = ℓ j / c a₀ * R a₀ := by
    intro j
    rcases (hℓ j).lt_or_eq with hj | hj
    · obtain ⟨C, hC, hjC⟩ := h.cover j hj
      rw [← himg] at hC
      obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hC
      refine ⟨a₀, fun R => ?_⟩
      rw [liftPt, Finset.sum_eq_single a₀]
      · simp only [hjC, ite_true]; rfl
      · intro b _ hb
        rw [ite_eq_right_iff]
        intro hjb
        exfalso
        exact Finset.disjoint_left.1 (h.disj _ (hGS b) _ (hGS a₀) (fun he => hb (hGi he)))
          hjb hjC
      · intro ha; exact absurd (Finset.mem_univ a₀) ha
    · refine ⟨0, fun R => ?_⟩
      simp [liftPt, ← hj]
  -- Lemma 17 for the final lengths
  have h17 : L17.Hyp17 (t 0) (t 1) (t 2) :=
    ⟨by linarith [hcle 0], by linarith [hcle 1], by linarith [hcle 2],
      by simp only [t]; linarith [hcpos 2], by simp only [t]; linarith [hcpos 0],
      by simp only [t]; linarith [hcpos 1]⟩
  obtain ⟨-, hw1, hmix, -⟩ := lem17 (hcpos 0) (hcpos 1) (hcpos 2) (by linarith [hcle 0])
    (by linarith [hcle 1]) (by linarith [hcle 2])
  rw [hs'] at hw1 hmix
  have hw := L17.w17_nonneg h17
  have hF : ∀ a, ∑ e, ENNReal.ofReal (L17.w17 (t 0) (t 1) (t 2) e) •
      unifI (min (L17.P17 (t 0) (t 1) (t 2) e a) (L17.Q17 (t 0) (t 1) (t 2) e a))
        (max (L17.P17 (t 0) (t 1) (t 2) e a) (L17.Q17 (t 0) (t 1) (t 2) e a)) = unifI 0 (c a) := by
    intro a
    rw [← segMix_map, hmix.2.2 a]
    fin_cases a <;> rfl
  have hPs : ∀ e, ∑ a, L17.P17 (t 0) (t 1) (t 2) e a = s := fun e => by
    fin_cases e <;> simp [L17.P17, L17.A17, L17.B17, Fin.sum_univ_three, t] <;> linarith
  have hQs : ∀ e, ∑ a, L17.Q17 (t 0) (t 1) (t 2) e a = s := fun e => by
    fin_cases e <;> simp [L17.Q17, L17.B17, L17.C17, Fin.sum_univ_three, t] <;> linarith
  have hlift : ∀ R : Fin 3 → ℝ, ∑ a, R a = s → ∑ j, liftPt ℓ G R j = s := by
    intro R hR
    rw [← hR]
    simp only [liftPt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have : ∑ j ∈ G a, ℓ j = c a := rfl
    rw [this, mul_inv_cancel₀ (hcpos a).ne', one_mul]
  have hFj : ∀ j, ∑ e, ENNReal.ofReal (L17.w17 (t 0) (t 1) (t 2) e) •
      unifI (min (liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e) j)
          (liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e) j))
        (max (liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e) j)
          (liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e) j)) =
      ENNReal.ofReal 1 • unifI 0 (ℓ j) := by
    intro j
    obtain ⟨a₀, ha₀⟩ := hcoord j
    simp only [ha₀]
    rw [ENNReal.ofReal_one, one_smul]
    have := mix_unifI_scale (L17.w17 (t 0) (t 1) (t 2)) (fun e => L17.P17 (t 0) (t 1) (t 2) e a₀)
      (fun e => L17.Q17 (t 0) (t 1) (t 2) e a₀) (t := ℓ j / c a₀)
      (div_nonneg (hℓ j) (hcpos a₀).le) (hcpos a₀).le hw hw1 (hF a₀)
    rw [div_mul_cancel₀ _ (hcpos a₀).ne'] at this
    exact this
  obtain ⟨hmix', hae⟩ := isJointMix_segMix (L17.w17 (t 0) (t 1) (t 2))
    (fun e => liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e))
    (fun e => liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e)) s 1 (fun j => unifI 0 (ℓ j)) hw hw1
    one_pos (fun e => hlift _ (hPs e)) (fun e => hlift _ (hQs e)) hFj
  simp only [div_one] at hmix' hae
  exact ⟨hmix', fun e => hlift _ (hPs e), fun e => hlift _ (hQs e), hae⟩

/-- **Lemma 18** (`j:lem:uni`), with the paper's procedure. Let `k ≥ 2`, `ℓ₁, …, ℓ_k ≥ 0` with
`s = (ℓ₁ + ⋯ + ℓ_k)/2 > 0` and `max ℓ_j ≤ s`.
(1) If exactly two lengths `ℓ_i, ℓ_j` are positive, they equal `s`, and the uniform distribution
on the segment from `s eᵢ` to `s eⱼ` (`Xᵢ = s(1 - V)`, `Xⱼ = s V`, the other coordinates `0`;
the paper's `Xᵢ = sV`, `Xⱼ = s(1 - V)` has the same law) is a joint mix of `U[0,ℓ₁], …, U[0,ℓ_k]`
with sum `s`, with endpoints in `H_s`.
(2) Otherwise (at least three positive lengths), the merging of two shortest lengths can be run
until three lengths remain, and for every such run (`MergeStep`, any choice among ties) and every
labelling `G 0, G 1, G 2` of the three final groups, Lemma 17 applied to the three remaining
lengths and composed with the substitutions `X_i = ℓ_i W/(ℓ_i + ℓ_j)` (`liftPt`) gives a joint
mix of `U[0,ℓ₁], …, U[0,ℓ_k]` with sum `s` that is a mixture of three (some possibly of weight
`0`) uniform distributions on segments with endpoints in `H_s`. -/
theorem res18 {ℓ : Fin k → ℝ} (hℓ : ∀ j, 0 ≤ ℓ j) (hs : 0 < (∑ j, ℓ j) / 2)
    (hmax : ∀ j, ℓ j ≤ (∑ j, ℓ j) / 2) :
    (∀ i j, i ≠ j → 0 < ℓ i → 0 < ℓ j → (∀ l, l ≠ i → l ≠ j → ℓ l = 0) →
      ℓ i = (∑ j, ℓ j) / 2 ∧ ℓ j = (∑ j, ℓ j) / 2 ∧
      IsJointMix (fun l => unifI 0 (ℓ l))
        (segMix (fun _ : Fin 1 => (1 : ℝ)) (fun _ => Pi.single i ((∑ j, ℓ j) / 2))
          (fun _ => Pi.single j ((∑ j, ℓ j) / 2))) ∧
      ∑ l, Pi.single (M := fun _ => ℝ) i ((∑ j, ℓ j) / 2) l = (∑ j, ℓ j) / 2 ∧
      ∑ l, Pi.single (M := fun _ => ℝ) j ((∑ j, ℓ j) / 2) l = (∑ j, ℓ j) / 2) ∧
    (2 < (initGroups ℓ).card →
      ∃ S, Relation.ReflTransGen (MergeStep ℓ) (initGroups ℓ) S ∧ S.card = 3) ∧
    (2 < (initGroups ℓ).card → ∀ S, Relation.ReflTransGen (MergeStep ℓ) (initGroups ℓ) S →
      S.card ≤ 3 → ∀ G : Fin 3 → Finset (Fin k), Function.Injective G → (∀ a, G a ∈ S) →
      let t : Fin 3 → ℝ := fun a => (∑ j, ℓ j) / 2 - glen ℓ (G a)
      IsJointMix (fun j => unifI 0 (ℓ j))
          (segMix (L17.w17 (t 0) (t 1) (t 2))
            (fun e => liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e))
            (fun e => liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e))) ∧
        (∀ e, ∑ j, liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e) j = (∑ j, ℓ j) / 2) ∧
        (∀ e, ∑ j, liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e) j = (∑ j, ℓ j) / 2) ∧
        ∀ᵐ x ∂segMix (L17.w17 (t 0) (t 1) (t 2))
            (fun e => liftPt ℓ G (L17.P17 (t 0) (t 1) (t 2) e))
            (fun e => liftPt ℓ G (L17.Q17 (t 0) (t 1) (t 2) e)), ∑ j, x j = (∑ j, ℓ j) / 2) := by
  set s := (∑ j, ℓ j) / 2 with hsdef
  have hsum : ∑ j, ℓ j = 2 * s := by rw [hsdef]; ring
  refine ⟨fun i j hij hi hj h0 => ?_, fun h3 => ?_, fun h3 S hS hS3 G hGi hGS => ?_⟩
  · have h2 : ∑ l, ℓ l = ℓ i + ℓ j := Fintype.sum_eq_add i j hij fun l hl => h0 l hl.1 hl.2
    have hi' : ℓ i = s := by linarith [hmax i, hmax j]
    have hj' : ℓ j = s := by linarith [hmax i, hmax j]
    have hPi : ∑ l, Pi.single (M := fun _ => ℝ) i s l = s := Fintype.sum_pi_single' i s
    have hPj : ∑ l, Pi.single (M := fun _ => ℝ) j s l = s := Fintype.sum_pi_single' j s
    refine ⟨hi', hj', ?_, hPi, hPj⟩
    obtain ⟨hmix, -⟩ := isJointMix_segMix (fun _ : Fin 1 => (1 : ℝ)) (fun _ => Pi.single i s)
      (fun _ => Pi.single j s) s 1 (fun l => unifI 0 (ℓ l)) (fun _ => zero_le_one) (by simp)
      one_pos (fun _ => hPi) (fun _ => hPj) (fun l => by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        by_cases hli : l = i
        · subst hli
          simp [Pi.single_eq_of_ne hij, hi', hs.le]
        by_cases hlj : l = j
        · subst hlj
          simp [Pi.single_eq_of_ne hli, hj', hs.le]
        · simp [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, h0 l hli hlj])
    simpa using hmix
  · exact exists_terminal _ _ rfl (minv_init hℓ hsum (fun j => hmax j) h3)
  · exact final_mix hℓ (minv_reach (minv_init hℓ hsum (fun j => hmax j) h3) hS) hS3 G hGi hGS

end Lemma18

end Mixes.Combined
