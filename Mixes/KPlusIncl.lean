import Mixes.ClassK
import Mixes.ScaledC

/-!
# `𝒦 ⊂ 𝒦⁺` (Definition 78, Theorem 79)

The sentence after Definition 78 (`g:def:class`) of `mixes/main.tex`: every member of the class
`𝒦` of Definition 60 is a member of `𝒦⁺`.

* `spF d`: the coordinate space `Fin d → ℝ` as an ambient space of `𝒦⁺`.
* `Reg K`: compact, convex, with nonempty interior; `Reg.image`, `reg_hullC`.
* `KPlus.transfer`: a bijective affine image of a member of `𝒦⁺`, as a set.
* `kplus_segment`: segments `{l ≤ x₀ ≤ r} ⊆ ℝ¹` (images of the ball `eBall 1`).
* `inK_subset_kPlus` (main theorem): `InK d K` implies `KPlus (spF d) (unifSet K) d`, i.e. the
  uniform distribution on `K` is a member of `𝒦⁺` of dimension `d` in the same space `ℝ^d`.
* `classK_scaling_of_kPlus`: the consequence that Theorem 79 (constant `d + 1`) recovers the
  scaling property of Theorem 61.
-/

open MeasureTheory Set Module Pointwise

noncomputable section

namespace Mixes

namespace KPlusIncl

open ClassK ScaledB ScaledC FrustumMix

/-- The coordinate space `ℝ^d = Fin d → ℝ` (sup norm, Lebesgue measure) as a space of `𝒦⁺`. -/
abbrev spF (d : ℕ) : Sp := ⟨Fin d → ℝ⟩

/-- Compact, convex, with nonempty interior. -/
structure Reg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) : Prop where
  cpt : IsCompact K
  cvx : Convex ℝ K
  int : (interior K).Nonempty

section Gen

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

lemma Reg.image {K : Set E} (h : Reg K) (L : E ≃L[ℝ] F) (b : F) :
    Reg ((fun x => L x + b) '' K) := by
  let H : E ≃ₜ F := L.toHomeomorph.trans (Homeomorph.addRight b)
  have hH : (fun x => L x + b) = H := rfl
  refine ⟨h.cpt.image (by fun_prop), ?_, ?_⟩
  · have : (fun x => L x + b) '' K = b +ᵥ (L '' K) := by
      rw [← image_vadd, image_image]; simp only [vadd_eq_add, add_comm]
    rw [this]
    exact (h.cvx.linear_image L.toLinearEquiv.toLinearMap).translate b
  · rw [hH, ← H.image_interior]
    exact h.int.image _

lemma Reg.prod {K₁ : Set E} {K₂ : Set F} (h₁ : Reg K₁) (h₂ : Reg K₂) : Reg (K₁ ×ˢ K₂) :=
  ⟨h₁.cpt.prod h₂.cpt, h₁.cvx.prod h₂.cvx, by rw [interior_prod_eq]; exact h₁.int.prod h₂.int⟩

variable [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma Reg.vol_ne_zero {K : Set E} (h : Reg K) : volume K ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior _ h.int).ne'

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma Reg.vol_ne_top {K : Set E} (h : Reg K) : volume K ≠ ⊤ :=
  h.cpt.measure_lt_top.ne

/-- A convex set of positive volume has nonempty interior. -/
lemma interior_nonempty_of_convex {K : Set E} (hc : Convex ℝ K) (hv : volume K ≠ 0) :
    (interior K).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hf := Convex.addHaar_frontier (volume : Measure E) hc
  rw [frontier, hne, sdiff_empty] at hf
  exact hv (measure_mono_null subset_closure hf)

end Gen

/-- A continuous linear equivalence from a linear measurable equivalence. -/
def toCLE {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
    (g : E ≃ᵐ F) (hlin : IsLinearMap ℝ g) : E ≃L[ℝ] F :=
  ({ IsLinearMap.mk' g hlin with
      invFun := g.symm, left_inv := g.left_inv, right_inv := g.right_inv } : E ≃ₗ[ℝ] F)
    |>.toContinuousLinearEquiv

@[simp] lemma toCLE_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E]
    [MeasurableSpace F] (g : E ≃ᵐ F) (hlin : IsLinearMap ℝ g) (x : E) :
    toCLE g hlin x = g x := rfl

/-- A bijective affine image of a member of `𝒦⁺` (given by a set) is a member of `𝒦⁺` of the
same dimension. -/
theorem KPlus.transfer {X Y : Sp} {K : Set X.carrier} {k : ℕ} (h : KPlus X (unifSet K) k)
    (L : X.carrier ≃L[ℝ] Y.carrier) (b : Y.carrier) :
    KPlus Y (unifSet ((fun x => L x + b) '' K)) k := by
  rw [unifSet_image_affineEquiv L b K]
  exact KPlus.affine h (L : X.carrier →L[ℝ] Y.carrier) L.injective b

/-! ### Points, balls, segments -/

lemma reg_point : Reg (univ : Set (Fin 0 → ℝ)) :=
  ⟨Set.subsingleton_of_subsingleton.isCompact, convex_univ, by
    rw [interior_univ]; exact univ_nonempty⟩

lemma kplus_point : KPlus (spF 0) (unifSet (univ : Set (Fin 0 → ℝ))) 0 := by
  have h := KPlus.point (spF 0)
  convert h using 1
  have := unifSet_isProb good_point.pos good_point.fin
  exact prob_eq_of_subsingleton _ _

/-- `eEuc` as a continuous linear equivalence. -/
def eEucL (j : ℕ) : EuclideanSpace ℝ (Fin j) ≃L[ℝ] (Fin j → ℝ) :=
  toCLE (eEuc j) ⟨fun _ _ => rfl, fun _ _ => rfl⟩

lemma eEucL_image (j : ℕ) :
    (fun x => eEucL j x + 0) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1 = eBall j := by
  rw [← eEuc_image_ball]; simp [eEucL]

lemma reg_eBall (j : ℕ) : Reg (eBall j) := by
  have h : Reg (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1) :=
    ⟨isCompact_closedBall _ _, convex_closedBall _ _,
      ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self one_pos)⟩⟩
  rw [← eEucL_image]; exact h.image _ _

lemma kplus_ball (j : ℕ) (hj : 1 ≤ j) : KPlus (spF j) (unifSet (eBall j)) j := by
  rw [← eEucL_image]; exact KPlus.transfer (Y := spF j) (KPlus.ball j hj) _ _

/-- The segment `{x ∈ ℝ¹ : l ≤ x₀ ≤ r}`. -/
def segSet (l r : ℝ) : Set (Fin 1 → ℝ) := {x | l ≤ x 0 ∧ x 0 ≤ r}

/-- The scaling `x ↦ c x` of `ℝ¹`. -/
def scL {c : ℝ} (hc : c ≠ 0) : (Fin 1 → ℝ) ≃L[ℝ] (Fin 1 → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin 1 → ℝ) c hc).toContinuousLinearEquiv

lemma segC_ne {l r : ℝ} (hlr : l < r) : (r - l) / 2 ≠ 0 := by
  have := sub_pos.2 hlr; positivity

lemma segSet_eq {l r : ℝ} (hlr : l < r) :
    segSet l r = (fun x => scL (segC_ne hlr) x + fun _ => (l + r) / 2) '' eBall 1 := by
  have hc : 0 < (r - l) / 2 := by linarith
  ext x
  simp only [segSet, eBall, mem_ofPred_eq, mem_image, Fin.sum_univ_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun _ => (x 0 - (l + r) / 2) / ((r - l) / 2), ?_, ?_⟩
    · rw [div_pow, div_le_one (by positivity)]
      nlinarith
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [scL, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp; ring
  · rintro ⟨y, hy, rfl⟩
    simp only [scL, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : -1 ≤ y 0 := by nlinarith
    have h2 : y 0 ≤ 1 := by nlinarith
    constructor <;> nlinarith

lemma reg_segSet {l r : ℝ} (hlr : l < r) : Reg (segSet l r) := by
  rw [segSet_eq hlr]; exact (reg_eBall 1).image _ _

lemma kplus_segSet {l r : ℝ} (hlr : l < r) : KPlus (spF 1) (unifSet (segSet l r)) 1 := by
  rw [segSet_eq hlr]; exact KPlus.transfer (Y := spF 1) (kplus_ball 1 le_rfl) _ _

/-! ### The hulls of Corollary 77 are regular -/

lemma reg_hullC {J : ℕ} [NeZero J] (X : Fin J → Sp) (F : (j : Fin J) → Set (X j).carrier)
    (hF : ∀ j, IsCompact (F j)) (hFc : ∀ j, Convex ℝ (F j))
    (hFi : ∀ j, (interior (F j)).Nonempty) (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (hab : ∀ j, 0 < a j + b j) (t : (j : Fin J) → (X j).carrier) :
    Reg (hullC F a b t) := by
  have hne : ∀ j, (F j).Nonempty := fun j => (hFi j).mono interior_subset
  have hcv : Convex ℝ (hullC F a b t) := convex_convexHull ℝ _
  refine ⟨?_, hcv, ?_⟩
  · rw [hullC_eq hFc hne ha hb]
    exact isCompact_bodyL (continuous_diagMap fun j => by unfold Scaled.prof; fun_prop)
      (by fun_prop) (isCompact_univ_pi hF)
  · have := (Sp.hull X).haar
    exact interior_nonempty_of_convex hcv (volume_hullC hF hFc hFi ha hb hab t).1

/-! ### Frusta and joins over `ℝ^0` are segments -/

lemma frustum_zero {q : ℝ} :
    eFr 0 '' frustumSet q (univ : Set (Fin 0 → ℝ)) = segSet q 1 := by
  ext x
  constructor
  · rintro ⟨p, ⟨h1, h2, -⟩, rfl⟩
    rw [eFr_apply]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(x 0, Fin.tail x), ⟨h1, h2, 0, mem_univ _, Subsingleton.elim _ _⟩, ?_⟩
    rw [eFr_apply]; exact Fin.cons_self_tail x

lemma join_zero :
    eJ 0 '' joinSet (univ : Set (Fin 0 → ℝ)) univ = segSet 0 1 := by
  ext x
  constructor
  · rintro ⟨p, ⟨h1, h2, -⟩, rfl⟩
    rw [eJ_apply, eFr_apply]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(x 0, (0, 0)), ⟨h1, h2, 0, mem_univ _, 0, mem_univ _, Subsingleton.elim _ _⟩, ?_⟩
    rw [eJ_apply, eFr_apply]
    conv_rhs => rw [← Fin.cons_self_tail x]
    congr 1
    funext i; exact i.elim0

/-! ### Joins of positive dimension are hulls -/

section JoinHull

variable {a : ℕ}

/-- The coordinates `(θ, y) ↦ (θ, y 0, y 1)`. -/
def pJ (p : ℝ × (Fin 2 → (Fin a → ℝ))) : ℝ × ((Fin a → ℝ) × (Fin a → ℝ)) := (p.1, (p.2 0, p.2 1))

/-- The join of convex nonempty sets is the hull of Corollary 77 with `J = 2`, `a = (1, 0)`,
`b = (0, 1)`, `t = 0`, in the coordinates `(θ, x, y)`. -/
lemma joinSet_eq_hull {K₁ K₂ : Set (Fin a → ℝ)} (h₁ : Convex ℝ K₁) (h₂ : Convex ℝ K₂)
    (n₁ : K₁.Nonempty) (n₂ : K₂.Nonempty) :
    joinSet K₁ K₂ = pJ '' hullC (V := fun _ : Fin 2 => Fin a → ℝ) ![K₁, K₂] ![1, 0] ![0, 1] 0 := by
  rw [hullC_eq (fun j => by fin_cases j <;> simpa) (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simp) (fun j => by fin_cases j <;> simp)]
  ext ⟨θ, x, y⟩
  simp only [joinSet, bodyL, secL, mem_ofPred_eq, mem_image, mem_prod, mem_Icc, mem_pi,
    mem_univ, true_implies, Prod.exists, pJ, Prod.mk.injEq, smul_zero, zero_add,
    Fin.forall_fin_two]
  constructor
  · rintro ⟨h0, h1, u, hu, v, hv, h⟩
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨θ, _, ⟨θ, ![u, v], ⟨⟨h0, h1⟩, by simpa, by simpa⟩, rfl, rfl⟩, rfl, ?_, ?_⟩ <;>
      simp [diagMap, Scaled.prof]
  · rintro ⟨s, z, ⟨s', w, ⟨⟨h0, h1⟩, hw0, hw1⟩, rfl, rfl⟩, rfl, rfl, rfl⟩
    refine ⟨h0, h1, w 0, by simpa using hw0, w 1, by simpa using hw1, ?_, ?_⟩ <;>
      simp [diagMap, Scaled.prof]

/-- The linear equivalence `ℝ × (ℝ^a)² ≃ ℝ^{2a+1}` of the joins. -/
def joinL (a : ℕ) : (ℝ × (Fin 2 → (Fin a → ℝ))) ≃L[ℝ] (Fin (a + a + 1) → ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.piFinTwo ℝ fun _ => Fin a → ℝ)).trans (toCLE (eJ a) (eJ_lin a))

lemma joinL_image {K₁ K₂ : Set (Fin a → ℝ)} (h₁ : Convex ℝ K₁) (h₂ : Convex ℝ K₂)
    (n₁ : K₁.Nonempty) (n₂ : K₂.Nonempty) :
    (fun x => joinL a x + 0) ''
      hullC (V := fun _ : Fin 2 => Fin a → ℝ) ![K₁, K₂] ![1, 0] ![0, 1] 0 =
      eJ a '' joinSet K₁ K₂ := by
  rw [joinSet_eq_hull h₁ h₂ n₁ n₂, image_image]
  congr 1
  funext p
  simp [joinL, pJ]

end JoinHull

/-! ### The inclusion -/

/-- **`𝒦 ⊂ 𝒦⁺`** (Definition 78, `g:def:class`), with the regularity carried along the
induction: every member `K ⊆ ℝ^d` of `𝒦` (Definition 60) is compact and convex with nonempty
interior, and its uniform distribution is a member of `𝒦⁺` of dimension `d` in `ℝ^d`. -/
theorem reg_and_kPlus {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) :
    Reg K ∧ KPlus (spF d) (unifSet K) d := by
  induction hK with
  | point => exact ⟨reg_point, kplus_point⟩
  | ball j hj => exact ⟨reg_eBall j, kplus_ball j hj⟩
  | @affine d K M hM b _ ih =>
    let L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
      (LinearMap.equivOfDetNeZero M hM).toContinuousLinearEquiv
    have e : (fun x => L x + b) = fun x => M x + b := rfl
    exact ⟨e ▸ ih.1.image L b, e ▸ KPlus.transfer (Y := spF d) ih.2 L b⟩
  | @prod d₁ d₂ K₁ K₂ _ _ ih₁ ih₂ =>
    have hP := KPlus.prod ih₁.2 ih₂.2
    rw [← unifSet_prod ih₁.1.vol_ne_zero ih₁.1.vol_ne_top ih₂.1.vol_ne_zero
      ih₂.1.vol_ne_top] at hP
    set L := toCLE (eProd d₁ d₂) (eProd_lin d₁ d₂)
    have e : (fun x => L x + 0) '' (K₁ ×ˢ K₂) = eProd d₁ d₂ '' K₁ ×ˢ K₂ := by simp [L]
    rw [← e]
    exact ⟨(ih₁.1.prod ih₂.1).image L 0, KPlus.transfer (Y := spF (d₁ + d₂)) hP L 0⟩
  | @frustum m B q hq0 hq1 _ ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hB : B = univ := (ih.1.int.mono interior_subset).eq_univ
      subst hB
      rw [frustum_zero]
      exact ⟨reg_segSet (by linarith), kplus_segSet (by linarith)⟩
    · have hk : KPlus (spF m) (unifSet B) (finrank ℝ (spF m).carrier) := by
        simpa using ih.2
      have hF := KPlus_frustum (spF m) ih.1.cpt ih.1.cvx ih.1.int hk (by simp; omega)
        hq0 hq1
      simp only [finrank_fin_fun] at hF
      rw [Nat.add_comm] at hF
      set L := toCLE (eFr m) (eFr_lin m)
      have e : (fun x => L x + 0) '' frustumSet q B = eFr m '' frustumSet q B := by simp [L]
      rw [← e]
      refine ⟨?_, KPlus.transfer (Y := spF (m + 1)) hF L 0⟩
      refine Reg.image ?_ L 0
      rw [frustumSet_eq_hull (spF m) ih.1.cvx (ih.1.int.mono interior_subset) hq0 hq1]
      exact (reg_hullC (fun _ : Fin 1 => spF m) (fun _ => B) (fun _ => ih.1.cpt)
        (fun _ => ih.1.cvx) (fun _ => ih.1.int) _ _ (fun _ => hq0) (fun _ => zero_le_one)
        (fun _ => by linarith) 0).image _ _
  | @join a K₁ K₂ _ _ ih₁ ih₂ =>
    have n₁ := ih₁.1.int.mono interior_subset
    have n₂ := ih₂.1.int.mono interior_subset
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [n₁.eq_univ, n₂.eq_univ, join_zero]
      exact ⟨reg_segSet one_pos, kplus_segSet one_pos⟩
    · rw [← joinL_image ih₁.1.cvx ih₂.1.cvx n₁ n₂]
      have hF : ∀ j : Fin 2, IsCompact (![K₁, K₂] j) := fun j => by
        fin_cases j; exacts [ih₁.1.cpt, ih₂.1.cpt]
      have hFc : ∀ j : Fin 2, Convex ℝ (![K₁, K₂] j) := fun j => by
        fin_cases j; exacts [ih₁.1.cvx, ih₂.1.cvx]
      have hFi : ∀ j : Fin 2, (interior (![K₁, K₂] j)).Nonempty := fun j => by
        fin_cases j; exacts [ih₁.1.int, ih₂.1.int]
      have ha' : ∀ j : Fin 2, (0 : ℝ) ≤ ![1, 0] j := fun j => by fin_cases j <;> simp
      have hb' : ∀ j : Fin 2, (0 : ℝ) ≤ ![0, 1] j := fun j => by fin_cases j <;> simp
      have hab' : ∀ j : Fin 2, (0 : ℝ) < ![1, 0] j + ![0, 1] j := fun j => by
        fin_cases j <;> simp
      refine ⟨(reg_hullC (fun _ : Fin 2 => spF a) ![K₁, K₂] hF hFc hFi _ _ ha' hb' hab'
        0).image _ _, ?_⟩
      have hH := KPlus.hull (fun _ : Fin 2 => spF a) ![K₁, K₂] hF hFc hFi
        (fun j => by fin_cases j; exacts [by simpa using ih₁.2, by simpa using ih₂.2])
        (fun _ => by simp; omega) _ _ ha' hb' hab' 0
      have e : 1 + ∑ _j : Fin 2, finrank ℝ (spF a).carrier = a + a + 1 := by
        simp only [finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
        omega
      rw [e] at hH
      exact KPlus.transfer (Y := spF (a + a + 1)) hH (joinL a) 0

/-- **`𝒦 ⊂ 𝒦⁺`** (Definition 78 and the sentence after it, `g:def:class`): the uniform
distribution on a member `K ⊆ ℝ^d` of `𝒦` (`InK d K`, Definition 60) is a member of `𝒦⁺` of
dimension `d`, in the same space `ℝ^d` (`Fin d → ℝ` with Lebesgue measure). -/
theorem inK_subset_kPlus {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) :
    KPlus (spF d) (unifSet K) d :=
  (reg_and_kPlus hK).2

/-- **Theorem 79 recovers Theorem 61** (scaling property): through `𝒦 ⊂ 𝒦⁺`, the constant
`d + 1` of Theorem 79 (`ScaledB.thm79`, with its cited hypotheses: Theorem 51 for balls and the
level-law bound of Theorems 73 (b) and 67) gives the constant `d + 1` of Theorem 61 for every
member `K ⊆ ℝ^d` of `𝒦`, without the frustum hypothesis `Thm27Frustum` of `ClassK`. -/
theorem classK_scaling_of_kPlus
    (Hball : ∀ j : ℕ, 1 ≤ j →
      ScalingProperty (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) 2)
    (Hlev : ∀ (J : ℕ) [NeZero J] (k : Fin J → ℕ) (a b : Fin J → ℝ), (∀ j, 0 ≤ a j) →
      (∀ j, 0 ≤ b j) → (∀ j, 0 < a j + b j) →
      ScalingProperty (levLaw (prodDens (Scaled.prof a b) k)) ((∑ j, (k j : ℝ)) + 2))
    {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) :
    ScalingProperty (unifSet K) ((d : ℝ) + 1) :=
  (thm79 Hball Hlev (inK_subset_kPlus hK)).2

/-- **Theorem 79 recovers Theorem 61** (complete mixes, `n ≥ max(2, d + 1)`). -/
theorem classK_completelyMixable_of_kPlus
    (Hball : ∀ j : ℕ, 1 ≤ j →
      ScalingProperty (unifSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)) 2)
    (Hlev : ∀ (J : ℕ) [NeZero J] (k : Fin J → ℕ) (a b : Fin J → ℝ), (∀ j, 0 ≤ a j) →
      (∀ j, 0 ≤ b j) → (∀ j, 0 < a j + b j) →
      ScalingProperty (levLaw (prodDens (Scaled.prof a b) k)) ((∑ j, (k j : ℝ)) + 2))
    {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ} (hn : 2 ≤ n) (hdn : d + 1 ≤ n) :
    CompletelyMixable n (unifSet K) :=
  thm79_completelyMixable Hball Hlev (inK_subset_kPlus hK) hn hdn

end KPlusIncl

end Mixes
