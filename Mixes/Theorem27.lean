import Mixes.JointSplit
import Mixes.JointLemmas
import Mixes.FrustumMix
import Mixes.Scaled
import Mixes.ConeMix
import Mixes.Homothetic

/-!
# Part II: the joint mix of Theorem 27 (`j:thm:main`), explicit and measurable

This file assembles Lemma 16 to Proposition 26 (files `Joint.lean`, `JointLemmas.lean`,
`JointSplit.lean`) into Theorem 27, with the measurability claim, and discharges the hypotheses
taken from Theorem 27 elsewhere.

## Construction

* `SegD n K`: segment data `(w, P, Q)` (weights, first and second endpoints of `K` segments in
  `ℝⁿ`); `Good s F d`: the weights are nonnegative and add up to `1`, the endpoints lie in
  `H_s`, and the marginals of `∑ wₑ ν_{[Pₑ,Qₑ]}` are the `F j` (a `SegRep` with explicit data).
* Explicit data, measurable in the parameters: `d17` (Lemma 17), `d18` (Lemma 18), `d24`
  (Proposition 24), `d26` (Proposition 26), and `leafD` (a leaf of Lemma 23, with a grouping
  in the spirit of the paragraph before Proposition 26; see `leafK`).
* `procMix`: the mixture over the leaves of Lemma 23, measurable in the pieces
  (`procMix_spec`, `measurable_procMix`).
* `exists_pieces`: Lemma 22 as a mixture `F = ∫ piece μ a b pd(da, db)`.
* `pieceMix`: the mixture over independently drawn pieces (`pieceMix_spec`).

## Main results

* `thm27` (for `F_j ∈ 𝒟(B_j)`), `thm27_concave` (as stated: concave distribution functions),
  with `necessity`; `dclass_of_concave` (concave distribution function ⟹ `𝒟(B)`).
* `cor_cm`, `cor_cm_concave` (Corollary 28, `j:cor:cm`), `cor30` (`Homothetic.Cor30 n`).
* Measurability: `exists_unif_rep` (a measurable family of laws is the law of a Borel function
  of the parameter and of independent uniform variables), `scaled_unif_rep` (Theorem 27 for
  scaled copies of one law, Borel in the scales).
* Consumers: `thm27Frustum` (`FrustumMix.Thm27Frustum m q` for `0 ≤ q < 1`),
  `thm27Frustum_all`, `thm27Frustum_zero`, the unconditional Corollaries 44 and 45
  (`simplex_jointlyMixable_iff'`, `simplex_completelyMixable_iff'`,
  `pyramid_completelyMixable_iff'`), `exists_hT27` and `thm73b_of_thm27` (`Scaled.thm73b`).
-/

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSimpArgs false

noncomputable section

namespace Mixes

namespace Theorem27

open JointSplit JointLemmas

/-! ### Segment data -/

/-- Segment data: weights `w`, first endpoints `P`, second endpoints `Q` of `K` segments. -/
abbrev SegD (n K : ℕ) := (Fin K → ℝ) × (Fin K → Fin n → ℝ) × (Fin K → Fin n → ℝ)

/-- The mixture `∑ₑ wₑ ν_{[Pₑ,Qₑ]}` of segment data. -/
def SegD.mix {n K : ℕ} (d : SegD n K) : Measure (Fin n → ℝ) := segMix d.1 d.2.1 d.2.2

/-- Good segment data for the marginals `F` and the sum `s`. -/
def Good {n K : ℕ} (s : ℝ) (F : Fin n → Measure ℝ) (d : SegD n K) : Prop :=
  (∀ e, 0 ≤ d.1 e) ∧ ∑ e, d.1 e = 1 ∧ (∀ e, ∑ j, d.2.1 e j = s) ∧ (∀ e, ∑ j, d.2.2 e j = s) ∧
    ∀ j, ∑ e, ENNReal.ofReal (d.1 e) • unifI (min (d.2.1 e j) (d.2.2 e j))
      (max (d.2.1 e j) (d.2.2 e j)) = F j

variable {n m K K' : ℕ}

lemma Good.segRep {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d) :
    SegRep s F := ⟨K, d.1, d.2.1, d.2.2, h⟩

/-- Good data give a joint mix with sum `s` (Lemma 16). -/
lemma Good.joint {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d) :
    IsJointMix F d.mix ∧ ∀ᵐ x ∂d.mix, ∑ j, x j = s := by
  obtain ⟨hw, hw1, hP, hQ, hF⟩ := h
  obtain ⟨hprob, hsum, -, hmap⟩ := seg_mix d.1 d.2.1 d.2.2 s hw hw1 hP hQ
  exact ⟨⟨hprob, ⟨s, hsum⟩, fun j => (hmap j).trans (hF j)⟩, hsum⟩

lemma Good.of_joint {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (hw : ∀ e, 0 ≤ d.1 e)
    (hw1 : ∑ e, d.1 e = 1) (hP : ∀ e, ∑ j, d.2.1 e j = s) (hQ : ∀ e, ∑ j, d.2.2 e j = s)
    (hmix : IsJointMix F d.mix) : Good s F d :=
  ⟨hw, hw1, hP, hQ, fun j => by rw [← segMix_map]; exact hmix.2.2 j⟩

lemma Good.congr {s s' : ℝ} {F F' : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d)
    (hs : s = s') (hF : ∀ j, F j = F' j) : Good s' F' d := by
  subst hs; obtain ⟨a, b, c, e, f⟩ := h; exact ⟨a, b, c, e, fun j => (f j).trans (hF j)⟩

/-- Affine images: coordinate `j` of the new vector is `c j * x (σ j) + t j`. -/
def SegD.affine (σ : Fin m → Fin n) (c t : Fin m → ℝ) (d : SegD n K) : SegD m K :=
  (d.1, fun e j => c j * d.2.1 e (σ j) + t j, fun e j => c j * d.2.2 e (σ j) + t j)

lemma Good.affine {s s' : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d)
    (σ : Fin m → Fin n) (c t : Fin m → ℝ)
    (hs : ∀ x : Fin n → ℝ, ∑ i, x i = s → ∑ j, (c j * x (σ j) + t j) = s') :
    Good s' (fun j => (F (σ j)).map (fun x => c j * x + t j)) (d.affine σ c t) := by
  obtain ⟨hw, hw1, hP, hQ, hF⟩ := h
  refine ⟨hw, hw1, fun e => hs _ (hP e), fun e => hs _ (hQ e), fun j => ?_⟩
  show _ = (F (σ j)).map (fun x => c j * x + t j)
  rw [← hF (σ j), Measure.map_finset_sum' (by fun_prop)]
  congr 1; funext e
  rw [Measure.map_smul, map_affine_seg]
  · rfl
  · fun_prop

/-- Affine images, with the coordinate sums checked at the endpoints only. -/
lemma Good.affine' {s s' : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d)
    (σ : Fin m → Fin n) (c t : Fin m → ℝ)
    (hsP : ∀ e, ∑ j, (c j * d.2.1 e (σ j) + t j) = s')
    (hsQ : ∀ e, ∑ j, (c j * d.2.2 e (σ j) + t j) = s') :
    Good s' (fun j => (F (σ j)).map (fun x => c j * x + t j)) (d.affine σ c t) := by
  obtain ⟨hw, hw1, hP, hQ, hF⟩ := h
  refine ⟨hw, hw1, hsP, hsQ, fun j => ?_⟩
  show _ = (F (σ j)).map (fun x => c j * x + t j)
  rw [← hF (σ j), Measure.map_finset_sum' (by fun_prop)]
  congr 1; funext e
  rw [Measure.map_smul, map_affine_seg]
  · rfl
  · fun_prop

/-- Mixing two segment data with the weights `t` and `1 - t` (concatenation). -/
def SegD.app (t : ℝ) (d1 : SegD n K) (d2 : SegD n K') : SegD n (K + K') :=
  (Fin.append (fun e => t * d1.1 e) (fun e => (1 - t) * d2.1 e), Fin.append d1.2.1 d2.2.1,
    Fin.append d1.2.2 d2.2.2)

lemma Good.app {s : ℝ} {F G : Fin n → Measure ℝ} {d1 : SegD n K} {d2 : SegD n K'}
    (h1 : Good s F d1) (h2 : Good s G d2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Good s (fun j => ENNReal.ofReal t • F j + ENNReal.ofReal (1 - t) • G j) (d1.app t d2) := by
  obtain ⟨hw1, hs1, hP1, hQ1, hF1⟩ := h1
  obtain ⟨hw2, hs2, hP2, hQ2, hG2⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_⟩
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.app, Fin.append_left]; exact mul_nonneg ht0 (hw1 e)
    · simp only [SegD.app, Fin.append_right]; exact mul_nonneg (by linarith) (hw2 e)
  · simp only [SegD.app]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← Finset.mul_sum, hs1, hs2]
    ring
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.app, Fin.append_left]; exact hP1 e
    · simp only [SegD.app, Fin.append_right]; exact hP2 e
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.app, Fin.append_left]; exact hQ1 e
    · simp only [SegD.app, Fin.append_right]; exact hQ2 e
  · simp only [SegD.app]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hF1 j, ← hG2 j, smul_mix_unifI ht0, smul_mix_unifI (by linarith)]

/-- Padding with segments of weight `0` (copies of `d` itself). -/
def SegD.pad (d : SegD n K) : SegD n (K + K) := d.app 1 d

lemma Good.pad {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n K} (h : Good s F d) :
    Good s F d.pad := by
  have := h.app h zero_le_one le_rfl
  refine this.congr rfl fun j => ?_
  simp

/-- Appending `r` copies of the first segment with weight `0`. -/
def SegD.padZ (r : ℕ) (d : SegD n (K + 1)) : SegD n (K + 1 + r) :=
  (Fin.append d.1 (fun _ => 0), Fin.append d.2.1 (fun _ => d.2.1 0),
    Fin.append d.2.2 (fun _ => d.2.2 0))

lemma Good.padZ {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n (K + 1)} (h : Good s F d) (r : ℕ) :
    Good s F (d.padZ r) := by
  obtain ⟨hw, hs, hP, hQ, hF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_⟩
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.padZ, Fin.append_left]; exact hw e
    · simp only [SegD.padZ, Fin.append_right]; exact le_rfl
  · simp only [SegD.padZ]; rw [Fin.sum_univ_add]; simp [hs]
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.padZ, Fin.append_left]; exact hP e
    · simp only [SegD.padZ, Fin.append_right]; exact hP 0
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simp only [SegD.padZ, Fin.append_left]; exact hQ e
    · simp only [SegD.padZ, Fin.append_right]; exact hQ 0
  · simp only [SegD.padZ]; rw [Fin.sum_univ_add]; simp [hF j]

/-- Normalising weights. -/
lemma good_norm {s : ℝ} {F : Fin n → Measure ℝ} (w : Fin K → ℝ) (P Q : Fin K → Fin n → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hpos : 0 < ∑ e, w e) (hP : ∀ e, ∑ j, P e j = s)
    (hQ : ∀ e, ∑ j, Q e j = s) (hmix : IsJointMix F (segMix (fun e => w e / ∑ e, w e) P Q)) :
    Good s F ((fun e => w e / ∑ e, w e, P, Q) : SegD n K) :=
  Good.of_joint (fun e => div_nonneg (hw e) hpos.le)
    (by simp only; rw [← Finset.sum_div, div_self hpos.ne']) hP hQ hmix

/-! ### Measurability of segment mixtures -/

lemma measurable_segMeasure :
    Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ) => segMeasure z.1 z.2 := by
  have := unifI_isProb 0 1
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hS : MeasurableSet {p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ |
      p.1.1 + p.2 • (p.1.2 - p.1.1) ∈ s} := (by fun_prop : Measurable fun
        p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => p.1.1 + p.2 • (p.1.2 - p.1.1)) hs
  have e : ∀ z : (Fin n → ℝ) × (Fin n → ℝ), segMeasure z.1 z.2 s =
      unifI 0 1 (Prod.mk z ⁻¹' {p | p.1.1 + p.2 • (p.1.2 - p.1.1) ∈ s}) := fun z => by
    rw [segMeasure, Measure.map_apply (measurable_segMap _ _) hs]; rfl
  simp_rw [e]
  exact measurable_measure_prodMk_left hS

lemma segD_mix_apply (s : Set (Fin n → ℝ)) (d : SegD n K) : d.mix s =
    ∑ e, ENNReal.ofReal (d.1 e) * segMeasure (d.2.1 e) (d.2.2 e) s := by
  unfold SegD.mix segMix
  rw [_root_.sum_apply]
  rfl

lemma measurable_segD_ends (e : Fin K) : Measurable fun d : SegD n K => (d.2.1 e, d.2.2 e) :=
  ((measurable_pi_apply e).comp (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd))

lemma measurable_segMix : Measurable fun d : SegD n K => d.mix := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [segD_mix_apply s]
  refine Finset.measurable_sum _ fun e _ => Measurable.mul ?_ ?_
  · exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply e).comp measurable_fst)
  · have h := (Measure.measurable_coe hs).comp
      ((measurable_segMeasure (n := n)).comp (measurable_segD_ends (K := K) e))
    exact h

/-! ### Measurability of data built from measurable parameters -/

section Meas

variable {X : Type*} [MeasurableSpace X]

lemma measurable_segD {w : X → Fin K → ℝ} {P Q : X → Fin K → Fin n → ℝ}
    (hw : ∀ e, Measurable fun x => w x e) (hP : ∀ e j, Measurable fun x => P x e j)
    (hQ : ∀ e j, Measurable fun x => Q x e j) :
    Measurable fun x => ((w x, P x, Q x) : SegD n K) :=
  (measurable_pi_iff.mpr hw).prodMk ((measurable_pi_iff.mpr fun e =>
    measurable_pi_iff.mpr (hP e)).prodMk (measurable_pi_iff.mpr fun e =>
      measurable_pi_iff.mpr (hQ e)))

lemma mW {d : X → SegD n K} (hd : Measurable d) (e : Fin K) :
    Measurable fun x => (d x).1 e := (measurable_pi_apply e).comp (measurable_fst.comp hd)

lemma mP {d : X → SegD n K} (hd : Measurable d) (e : Fin K) (j : Fin n) :
    Measurable fun x => (d x).2.1 e j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply e).comp
    (measurable_fst.comp (measurable_snd.comp hd)))

lemma mQ {d : X → SegD n K} (hd : Measurable d) (e : Fin K) (j : Fin n) :
    Measurable fun x => (d x).2.2 e j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply e).comp
    (measurable_snd.comp (measurable_snd.comp hd)))

lemma mAffine {d : X → SegD n K} (hd : Measurable d) (σ : Fin m → Fin n)
    {c t : X → Fin m → ℝ} (hc : ∀ j, Measurable fun x => c x j)
    (ht : ∀ j, Measurable fun x => t x j) :
    Measurable fun x => (d x).affine σ (c x) (t x) :=
  measurable_segD (fun e => mW hd e) (fun e j => ((hc j).mul (mP hd e (σ j))).add (ht j))
    (fun e j => ((hc j).mul (mQ hd e (σ j))).add (ht j))

lemma mApp {d1 : X → SegD n K} {d2 : X → SegD n K'} (hd1 : Measurable d1)
    (hd2 : Measurable d2) {t : X → ℝ} (ht : Measurable t) :
    Measurable fun x => (d1 x).app (t x) (d2 x) := by
  refine measurable_segD (fun e => ?_) (fun e j => ?_) (fun e j => ?_) <;>
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
  · simp only [Fin.append_left]; exact ht.mul (mW hd1 e)
  · simp only [Fin.append_right]; exact (measurable_const.sub ht).mul (mW hd2 e)
  · simp only [Fin.append_left]; exact mP hd1 e j
  · simp only [Fin.append_right]; exact mP hd2 e j
  · simp only [Fin.append_left]; exact mQ hd1 e j
  · simp only [Fin.append_right]; exact mQ hd2 e j

lemma mPad {d : X → SegD n K} (hd : Measurable d) :
    Measurable fun x => (d x).pad := mApp hd hd measurable_const

/-- Composition with a measurable index into a finite type. -/
lemma measurable_comp_fin {Y : Type*} [MeasurableSpace Y] {k : ℕ} {g : X → Fin k}
    (hg : Measurable g) {F : X → Fin k → Y} (hF : ∀ i, Measurable fun x => F x i) :
    Measurable fun x => F x (g x) := by
  have h : Measurable fun p : X × Fin k => F p.1 p.2 :=
    measurable_from_prod_countable_left fun i => hF i
  exact h.comp (measurable_id.prodMk hg)

lemma mAffineVar {d : X → SegD n K} (hd : Measurable d) {σ : X → Fin m → Fin n}
    (hσ : ∀ j, Measurable fun x => σ x j)
    {c t : X → Fin m → ℝ} (hc : ∀ j, Measurable fun x => c x j)
    (ht : ∀ j, Measurable fun x => t x j) :
    Measurable fun x => (d x).affine (σ x) (c x) (t x) :=
  measurable_segD (fun e => mW hd e)
    (fun e j => measurable_comp_fin (F := fun x i => c x j * (d x).2.1 e i + t x j) (hσ j)
      fun i => ((hc j).mul (mP hd e i)).add (ht j))
    (fun e j => measurable_comp_fin (F := fun x i => c x j * (d x).2.2 e i + t x j) (hσ j)
      fun i => ((hc j).mul (mQ hd e i)).add (ht j))

lemma mPadZ {d : X → SegD n (K + 1)} (hd : Measurable d) (r : ℕ) :
    Measurable fun x => (d x).padZ r := by
  refine measurable_segD (fun e => ?_) (fun e j => ?_) (fun e j => ?_) <;>
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
  · simp only [Fin.append_left]; exact mW hd e
  · simp only [Fin.append_right]; exact measurable_const
  · simp only [Fin.append_left]; exact mP hd e j
  · simp only [Fin.append_right]; exact mP hd 0 j
  · simp only [Fin.append_left]; exact mQ hd e j
  · simp only [Fin.append_right]; exact mQ hd 0 j

lemma measurable_norm {w : X → Fin K → ℝ} {P Q : X → Fin K → Fin n → ℝ}
    (hw : ∀ e, Measurable fun x => w x e) (hP : ∀ e j, Measurable fun x => P x e j)
    (hQ : ∀ e j, Measurable fun x => Q x e j) :
    Measurable fun x => ((fun e => w x e / ∑ e, w x e, P x, Q x) : SegD n K) :=
  measurable_segD (fun e => (hw e).div (Finset.measurable_sum _ fun e _ => hw e)) hP hQ

end Meas

/-! ### Lemma 17 and the groups of Lemma 18 -/

/-- The half sum `(c₀ + c₁ + c₂)/2`. -/
def half3 (c : Fin 3 → ℝ) : ℝ := (c 0 + c 1 + c 2) / 2

/-- The segment data of Lemma 17 for the lengths `c`. -/
def d17 (c : Fin 3 → ℝ) : SegD 3 3 :=
  (L17.w17 (half3 c - c 0) (half3 c - c 1) (half3 c - c 2),
    L17.P17 (half3 c - c 0) (half3 c - c 1) (half3 c - c 2),
    L17.Q17 (half3 c - c 0) (half3 c - c 1) (half3 c - c 2))

lemma good_d17 {c : Fin 3 → ℝ} (hc : ∀ i, 0 < c i) (hcs : ∀ i, c i ≤ half3 c) :
    Good (half3 c) (fun i => unifI 0 (c i)) (d17 c) := by
  have h1 := hcs 0; have h2 := hcs 1; have h3 := hcs 2
  simp only [half3] at h1 h2 h3
  obtain ⟨-, hw1, hmix, -⟩ := lem17 (hc 0) (hc 1) (hc 2) h1 h2 h3
  have hh : L17.Hyp17 (half3 c - c 0) (half3 c - c 1) (half3 c - c 2) := by
    have := hc 0; have := hc 1; have := hc 2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [half3] <;> linarith
  refine Good.of_joint (L17.w17_nonneg hh) hw1 ?_ ?_ ?_
  · intro e; fin_cases e <;>
      simp [d17, L17.P17, L17.A17, L17.B17, Fin.sum_univ_three, half3] <;> ring
  · intro e; fin_cases e <;>
      simp [d17, L17.Q17, L17.B17, L17.C17, Fin.sum_univ_three, half3] <;> ring
  · convert hmix using 2 with i
    fin_cases i <;> rfl
    rfl

lemma measurable_d17 {X : Type*} [MeasurableSpace X] {c : X → Fin 3 → ℝ}
    (hc : ∀ i, Measurable fun x => c x i) : Measurable fun x => d17 (c x) := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2
  refine measurable_segD (fun e => ?_) (fun e j => ?_) (fun e j => ?_)
  · fin_cases e <;> simp [L17.w17, half3] <;> fun_prop
  · fin_cases e <;> fin_cases j <;>
      simp [L17.P17, L17.A17, L17.B17, half3] <;> fun_prop
  · fin_cases e <;> fin_cases j <;>
      simp [L17.Q17, L17.B17, L17.C17, half3] <;> fun_prop

/-- Endpoints vanish on the coordinates with `C i = 0`. -/
def Van {K : ℕ} (C : Fin 3 → ℝ) (d : SegD 3 K) : Prop :=
  ∀ e i, C i = 0 → d.2.1 e i = 0 ∧ d.2.2 e i = 0

/-- One segment for two lengths `s` and one length `0` (at `i₀`). -/
def dZ (i0 : Fin 3) (s : ℝ) : SegD 3 1 :=
  (fun _ => 1, fun _ => if i0 = 0 then ![0, s, 0] else ![s, 0, 0],
    fun _ => if i0 = 2 then ![0, s, 0] else ![0, 0, s])

lemma good_dZ {s : ℝ} (hs0 : 0 ≤ s) {C : Fin 3 → ℝ} (i0 : Fin 3) (h0 : C i0 = 0)
    (hs : ∀ i, i ≠ i0 → C i = s) :
    Good s (fun i => unifI 0 (C i)) (dZ i0 s) ∧ Van C (dZ i0 s) := by
  refine ⟨⟨fun _ => zero_le_one, by simp [dZ], fun e => ?_, fun e => ?_, fun i => ?_⟩,
    fun e i hi => ?_⟩
  · simp only [dZ]; split_ifs <;> simp [Fin.sum_univ_three]
  · simp only [dZ]; split_ifs <;> simp [Fin.sum_univ_three]
  · simp only [dZ, Finset.univ_unique, Finset.sum_singleton, ENNReal.ofReal_one, one_smul]
    fin_cases i0 <;> fin_cases i <;>
      simp_all [unifI_self, min_eq_right, max_eq_left, max_eq_right]
  · have hs' : s ≠ 0 ∨ s = 0 := em' _
    rcases hs' with hs' | hs'
    · have : i = i0 := by
        by_contra hne; exact hs' ((hs i hne).symm.trans hi)
      subst this
      fin_cases i <;> simp [dZ]
    · subst hs'; simp only [dZ]; split_ifs <;> fin_cases i <;> simp

/-- Three copies of a single segment (two of weight `0`). -/
def SegD.pad3 (d : SegD n 1) : SegD n 3 := d.app 1 d.pad

lemma Good.pad3 {s : ℝ} {F : Fin n → Measure ℝ} {d : SegD n 1} (h : Good s F d) :
    Good s F d.pad3 := by
  have := h.app h.pad zero_le_one le_rfl
  refine this.congr rfl fun j => ?_
  simp

lemma Van.pad3 {C : Fin 3 → ℝ} {d : SegD 3 1} (h : Van C d) : Van C d.pad3 := by
  intro e i hi
  have := h 0 i hi
  fin_cases e <;> simpa [SegD.pad3, SegD.app, SegD.pad, Fin.append, Fin.addCases] using this

/-- The data for three group lengths `C` with `C₀ + C₁ + C₂ = 2s`: Lemma 17 if all are
positive, otherwise one segment. -/
def gd3 (C : Fin 3 → ℝ) (s : ℝ) : SegD 3 3 :=
  if C 0 ≤ 0 then (dZ 0 s).pad3 else if C 1 ≤ 0 then (dZ 1 s).pad3 else
    if C 2 ≤ 0 then (dZ 2 s).pad3 else d17 C

lemma good_gd3 {s : ℝ} (hs : 0 < s) {C : Fin 3 → ℝ} (hC0 : ∀ i, 0 ≤ C i) (hCs : ∀ i, C i ≤ s)
    (hsum : C 0 + C 1 + C 2 = 2 * s) :
    Good s (fun i => unifI 0 (C i)) (gd3 C s) ∧ Van C (gd3 C s) := by
  have zc : ∀ i0 : Fin 3, C i0 ≤ 0 → Good s (fun i => unifI 0 (C i)) (dZ i0 s).pad3 ∧
      Van C (dZ i0 s).pad3 := by
    intro i0 hi0
    have h0 : C i0 = 0 := le_antisymm hi0 (hC0 i0)
    have := hCs 0; have := hCs 1; have := hCs 2
    obtain ⟨h1, h2⟩ := good_dZ hs.le i0 h0 (fun i hi => by
      fin_cases i0 <;> fin_cases i <;> simp at hi h0 ⊢ <;> linarith)
    exact ⟨h1.pad3, h2.pad3⟩
  unfold gd3
  split_ifs with h0 h1 h2
  · exact zc 0 h0
  · exact zc 1 h1
  · exact zc 2 h2
  · push Not at h0 h1 h2
    have hpos : ∀ i, 0 < C i := fun i => by fin_cases i <;> assumption
    have hh : half3 C = s := by simp only [half3]; linarith
    refine ⟨(good_d17 hpos fun i => hh ▸ hCs i).congr hh (fun _ => rfl),
      fun e i hi => absurd hi (hpos i).ne'⟩

lemma measurable_dZ {X : Type*} [MeasurableSpace X] (i0 : Fin 3) {s : X → ℝ}
    (hs : Measurable s) : Measurable fun x => dZ i0 (s x) := by
  refine measurable_segD (fun e => measurable_const) (fun e j => ?_) (fun e j => ?_) <;>
    fin_cases i0 <;> fin_cases j <;> simp [dZ] <;> fun_prop

lemma measurable_gd3 {X : Type*} [MeasurableSpace X] {C : X → Fin 3 → ℝ} {s : X → ℝ}
    (hC : ∀ i, Measurable fun x => C x i) (hs : Measurable s) :
    Measurable fun x => gd3 (C x) (s x) := by
  have hz : ∀ i0, Measurable fun x => (dZ i0 (s x)).pad3 := fun i0 =>
    mApp (measurable_dZ i0 hs) (mPad (measurable_dZ i0 hs)) measurable_const
  unfold gd3
  refine Measurable.ite (measurableSet_le (hC 0) measurable_const) (hz 0) ?_
  refine Measurable.ite (measurableSet_le (hC 1) measurable_const) (hz 1) ?_
  exact Measurable.ite (measurableSet_le (hC 2) measurable_const) (hz 2) (measurable_d17 hC)

/-! ### Lemma 18 with explicit data -/

/-- Lifting group data to the original coordinates: `x_j = ℓ_j / C_{g j} · W_{g j}`. -/
lemma good_lift {k : ℕ} {s : ℝ} (ℓ : Fin k → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) (g : Fin k → Fin 3)
    (C : Fin 3 → ℝ) (hC : ∀ i, C i = ∑ j, if g j = i then ℓ j else 0) {d : SegD 3 K}
    (hd : Good s (fun i => unifI 0 (C i)) d) (hv : Van C d) :
    Good s (fun j => unifI 0 (ℓ j)) (d.affine g (fun j => ℓ j / C (g j)) 0) := by
  classical
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    rw [hC i]; exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hℓ]
  have hlC : ∀ j, ℓ j ≤ C (g j) := fun j => by
    have := Finset.single_le_sum (f := fun j' => if g j' = g j then ℓ j' else 0)
      (fun j' _ => by split_ifs <;> simp [hℓ]) (Finset.mem_univ j)
    rw [hC]; simpa using this
  have hlift : ∀ R : Fin K → Fin 3 → ℝ, (∀ e, ∑ i, R e i = s) →
      (∀ e i, C i = 0 → R e i = 0) →
      ∀ e, ∑ j, (ℓ j / C (g j) * R e (g j) + (0 : Fin k → ℝ) j) = s := by
    intro R hR hRZ e
    simp only [Pi.zero_apply, add_zero]
    rw [← hR e]
    rw [← Finset.sum_fiberwise Finset.univ g]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : ∀ j ∈ Finset.univ.filter (fun j => g j = i),
        ℓ j / C (g j) * R e (g j) = ℓ j * (R e i / C i) := by
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]; ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    have hCi : ∑ j ∈ Finset.univ.filter (fun j => g j = i), ℓ j = C i := by
      rw [hC i, Finset.sum_filter]
    rw [hCi]
    by_cases h : C i = 0
    · rw [h, hRZ e i h]; simp
    · field_simp
  have h := hd.affine' g (fun j => ℓ j / C (g j)) 0
    (hlift _ hd.2.2.1 fun e i hi => (hv e i hi).1)
    (hlift _ hd.2.2.2.1 fun e i hi => (hv e i hi).2)
  refine h.congr rfl fun j => ?_
  simp only [Pi.zero_apply, add_zero]
  by_cases h0 : C (g j) = 0
  · have : ℓ j = 0 := le_antisymm (h0 ▸ hlC j) (hℓ j)
    rw [h0, this, zero_div, unifI_self, Measure.map_dirac' (by fun_prop)]
    simp [unifI_self]
  · have := map_scale_unif (div_nonneg (hℓ j) (hC0 (g j))) (hC0 (g j))
    simp only [add_zero] at this
    rw [this, div_mul_cancel₀ _ h0]

/-- The groups of Lemma 18: lengths cut at `s = (∑ ℓ)/2`. -/
def g18 {k : ℕ} (ℓ : Fin k → ℝ) (j : Fin k) : Fin 3 := L18.grp (L18.ext ℓ) ((∑ j, ℓ j) / 2) j.val

/-- The group totals. -/
def C18 {k : ℕ} (ℓ : Fin k → ℝ) (i : Fin 3) : ℝ := ∑ j, if g18 ℓ j = i then ℓ j else 0

/-- The segment data of Lemma 18. -/
def d18 {k : ℕ} (ℓ : Fin k → ℝ) : SegD k 3 :=
  (gd3 (C18 ℓ) ((∑ j, ℓ j) / 2)).affine (g18 ℓ) (fun j => ℓ j / C18 ℓ (g18 ℓ j)) 0

/-- **Lemma 18** (`j:lem:uni`) with explicit data: for `ℓ ≥ 0` with `s = (∑ ℓ)/2 > 0` and
`max ℓ ≤ s`, `d18 ℓ` is a mixture of at most three uniform distributions on segments in `H_s`
that is a joint mix of the `U[0, ℓ_j]`. -/
theorem good_d18 {k : ℕ} (ℓ : Fin k → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) (hs : 0 < (∑ j, ℓ j) / 2)
    (hmax : ∀ j, ℓ j ≤ (∑ j, ℓ j) / 2) :
    Good ((∑ j, ℓ j) / 2) (fun j => unifI 0 (ℓ j)) (d18 ℓ) := by
  classical
  set s := (∑ j, ℓ j) / 2 with hsdef
  have hsum : ∑ j, ℓ j = 2 * s := by rw [hsdef]; ring
  have hC0 : ∀ i, 0 ≤ C18 ℓ i := fun i =>
    Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hℓ]
  have hCs : ∀ i, C18 ℓ i ≤ s := fun i => L18.group_sum_le ℓ hℓ hsum hs.le hmax i
  have hCsum : C18 ℓ 0 + C18 ℓ 1 + C18 ℓ 2 = 2 * s := by
    rw [← hsum, ← Fin.sum_univ_three (f := C18 ℓ)]
    simp only [C18]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  obtain ⟨hg, hv⟩ := good_gd3 hs hC0 hCs hCsum
  exact good_lift ℓ hℓ (g18 ℓ) (C18 ℓ) (fun i => rfl) hg hv

lemma measurable_S {X : Type*} [MeasurableSpace X] {k : ℕ} {ℓ : X → Fin k → ℝ}
    (hℓ : ∀ j, Measurable fun x => ℓ x j) (N : ℕ) :
    Measurable fun x => L18.S (L18.ext (ℓ x)) N := by
  unfold L18.S
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold L18.ext
  by_cases h : i < k
  · simp only [h, dite_true]; exact hℓ _
  · simp only [h, dite_false]; exact measurable_const

lemma measurable_grp {X : Type*} [MeasurableSpace X] {k : ℕ} {ℓ : X → Fin k → ℝ}
    (hℓ : ∀ j, Measurable fun x => ℓ x j) {s : X → ℝ} (hs : Measurable s) (j : ℕ) :
    Measurable fun x => L18.grp (L18.ext (ℓ x)) (s x) j := by
  unfold L18.grp
  exact Measurable.ite (measurableSet_le (measurable_S hℓ _) hs) measurable_const
    (Measurable.ite (measurableSet_le hs (measurable_S hℓ _)) measurable_const measurable_const)

lemma measurable_d18 {X : Type*} [MeasurableSpace X] {k : ℕ} {ℓ : X → Fin k → ℝ}
    (hℓ : ∀ j, Measurable fun x => ℓ x j) : Measurable fun x => d18 (ℓ x) := by
  have hs : Measurable fun x => (∑ j, ℓ x j) / 2 :=
    (Finset.measurable_sum _ fun j _ => hℓ j).div_const _
  have hg : ∀ j, Measurable fun x => g18 (ℓ x) j := fun j => measurable_grp hℓ hs j.val
  have hC : ∀ i, Measurable fun x => C18 (ℓ x) i := fun i =>
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (measurableSet_eq_fun (hg j) measurable_const) (hℓ j) measurable_const
  unfold d18
  exact mAffineVar (measurable_gd3 hC hs) hg (fun j => measurable_comp_fin
    (F := fun x i => ℓ x j / C18 (ℓ x) i) (hg j) fun i => (hℓ j).div (hC i))
    (fun j => measurable_const)

/-! ### Proposition 24 with explicit data -/

open P24 in
/-- The data of Proposition 24 in the parameters `y₁ ≤ y₂, σ, a, b` (case by case). -/
def raw24 (y1 y2 σ a b : ℝ) : SegD 3 5 :=
  if y2 ≤ a then (fun e => wI y1 y2 σ a b e / ∑ e, wI y1 y2 σ a b e, PI y1 y2 σ a b, QI y1 y2 σ)
  else if y1 = 0 then
    SegD.padZ 2 ((fun e => wII0 y1 y2 σ a b e / ∑ e, wII0 y1 y2 σ a b e, PII0 y1 y2 σ a b,
      QII0 y1 y2 σ a) : SegD 3 3)
  else if y1 ≤ a then
    (fun e => wII y1 y2 σ a b e / ∑ e, wII y1 y2 σ a b e, PII y1 y2 σ a b, QII y1 y2 σ a)
  else if σ + y1 ≤ b then
    (fun e => wIIIa y1 y2 σ a b e / ∑ e, wIIIa y1 y2 σ a b e, PIIIa y1 y2 σ a b, QIIIa y1 y2 σ b)
  else
    (fun e => wIIIb y1 y2 σ a b e / ∑ e, wIIIb y1 y2 σ a b e, PIIIb y1 y2 σ a, QIIIb y1 y2 σ a b)

open P24 in
lemma good_raw24 {y1 y2 σ a b : ℝ} (h : Hyp y1 y2 σ a b) :
    Good (σ + y1 + y2) ![unifI 0 (σ + y2), unifI 0 (σ + y1), gPiece ((y1 + y2) / 2) a b]
      (raw24 y1 y2 σ a b) := by
  have hy1 := h.hy1
  unfold raw24
  split_ifs with c1 c2 c3 c4
  · exact good_norm _ _ _ (wI_nonneg h c1) (wI_sum_pos h c1) PI_mem QI_mem (caseI_mix h c1).1
  · exact (good_norm _ _ _ (wII0_nonneg h c2) (wII0_sum_pos h c2) PII0_mem QII0_mem
      (caseII0_mix h c2).1).padZ 2
  · have hp : 0 < y1 := lt_of_le_of_ne hy1 (Ne.symm c2)
    push Not at c1
    exact good_norm _ _ _ (wII_nonneg h c3 c1 hp) (wII_sum_pos h c3 c1 hp) PII_mem QII_mem
      (caseII_mix h c3 c1 hp).1
  · push Not at c3
    exact good_norm _ _ _ (wIIIa_nonneg h c3 c4) (wIIIa_sum_pos h c3 c4) PIIIa_mem QIIIa_mem
      (caseIIIa_mix h c3 c4).1
  · push Not at c3 c4
    exact good_norm _ _ _ (wIIIb_nonneg h c3 c4) (wIIIb_sum_pos h c3 c4) PIIIb_mem QIIIb_mem
      (caseIIIb_mix h c3 c4).1

open P24 in
lemma measurable_raw24 {X : Type*} [MeasurableSpace X] {y1 y2 σ a b : X → ℝ}
    (h1 : Measurable y1) (h2 : Measurable y2) (h3 : Measurable σ) (h4 : Measurable a)
    (h5 : Measurable b) : Measurable fun x => raw24 (y1 x) (y2 x) (σ x) (a x) (b x) := by
  unfold raw24
  refine Measurable.ite (measurableSet_le h2 h4) ?_ ?_
  · refine measurable_norm (fun e => ?_) (fun e j => ?_) (fun e j => ?_)
    · fin_cases e <;> simp [wI, K] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [PI, A, B] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [QI, B, C] <;> fun_prop
  refine Measurable.ite (measurableSet_eq_fun h1 measurable_const) ?_ ?_
  · refine mPadZ (measurable_norm (fun e => ?_) (fun e j => ?_) (fun e j => ?_)) 2
    · fin_cases e <;> simp [wII0] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [PII0, A, D] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [QII0, C, D] <;> fun_prop
  refine Measurable.ite (measurableSet_le h1 h4) ?_ ?_
  · refine measurable_norm (fun e => ?_) (fun e j => ?_) (fun e j => ?_)
    · fin_cases e <;> simp [wII, K] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [PII, A, B, D] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [QII, B, C, D] <;> fun_prop
  refine Measurable.ite (measurableSet_le (h3.add h1) h5) ?_ ?_
  · refine measurable_norm (fun e => ?_) (fun e j => ?_) (fun e j => ?_)
    · fin_cases e <;> simp [wIIIa, N2, N4] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [PIIIa, A', D'] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [QIIIa, A', B, E] <;> fun_prop
  · refine measurable_norm (fun e => ?_) (fun e j => ?_) (fun e j => ?_)
    · fin_cases e <;> simp [wIIIb, N2] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [PIIIb, B, D'] <;> fun_prop
    · fin_cases e <;> fin_cases j <;> simp [QIIIb, A, A', D'] <;> fun_prop

/-- The sum `s = (c₁ + c₂)/2 + μ` of Proposition 24. -/
def s24 (c1 c2 μ : ℝ) : ℝ := (c1 + c2) / 2 + μ

/-- **Proposition 24** with explicit data (both orders of `c₁, c₂`). -/
def d24 (c1 c2 μ a b : ℝ) : SegD 3 5 :=
  if c2 ≤ c1 then raw24 (s24 c1 c2 μ - c1) (s24 c1 c2 μ - c2) (s24 c1 c2 μ - 2 * μ) a b
  else (raw24 (s24 c1 c2 μ - c2) (s24 c1 c2 μ - c1) (s24 c1 c2 μ - 2 * μ) a b).affine
    ![1, 0, 2] (fun _ => 1) (fun _ => 0)

theorem good_d24 {c1 c2 μ a b : ℝ} (ha : 0 ≤ a) (ha2 : a < 2 * μ) (hb : 2 * μ < b)
    (hc1s : c1 ≤ s24 c1 c2 μ) (hc2s : c2 ≤ s24 c1 c2 μ) (hbs : b ≤ s24 c1 c2 μ) :
    Good (s24 c1 c2 μ) ![unifI 0 c1, unifI 0 c2, gPiece μ a b] (d24 c1 c2 μ a b) := by
  set s := s24 c1 c2 μ with hs
  have hsd : s = (c1 + c2) / 2 + μ := rfl
  unfold d24
  split_ifs with h12
  · have hyp : P24.Hyp (s - c1) (s - c2) (s - 2 * μ) a b :=
      ⟨by linarith, by linarith, ha, by linarith, by linarith, by linarith⟩
    refine (good_raw24 hyp).congr (by linarith) fun j => ?_
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]; congr 1; linarith
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; congr 1; linarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val]; congr 1; linarith
  · have hyp : P24.Hyp (s - c2) (s - c1) (s - 2 * μ) a b :=
      ⟨by linarith, by linarith, ha, by linarith, by linarith, by linarith⟩
    have h := (good_raw24 hyp).affine ![1, 0, 2] (fun _ => 1) (fun _ => 0) (s' := s)
      (fun x hx => by simp [Fin.sum_univ_three] at hx ⊢; linarith)
    refine h.congr rfl fun j => ?_
    simp only [one_mul, add_zero, Measure.map_id']
    fin_cases j
    · simp; congr 1; linarith
    · simp; congr 1; linarith
    · simp; congr 1; linarith

lemma measurable_d24 {X : Type*} [MeasurableSpace X] {c1 c2 μ a b : X → ℝ}
    (h1 : Measurable c1) (h2 : Measurable c2) (h3 : Measurable μ) (h4 : Measurable a)
    (h5 : Measurable b) : Measurable fun x => d24 (c1 x) (c2 x) (μ x) (a x) (b x) := by
  have hs : Measurable fun x => s24 (c1 x) (c2 x) (μ x) := by unfold s24; fun_prop
  unfold d24
  refine Measurable.ite (measurableSet_le h2 h1) ?_ ?_
  · exact measurable_raw24 (hs.sub h1) (hs.sub h2) (hs.sub (h3.const_mul 2)) h4 h5
  · exact mAffine (measurable_raw24 (hs.sub h2) (hs.sub h1) (hs.sub (h3.const_mul 2)) h4 h5) _
      (fun _ => measurable_const) (fun _ => measurable_const)

/-! ### Proposition 26 with explicit data -/

/-- The length of `L̄ = U[0, r]` when `κ` is at an end of `[qC, C]`. -/
def rU (p q C κ : ℝ) : ℝ := if q * C < κ then C else p * C

lemma rU_spec {p q C κ : ℝ} (h : KHyp p q C κ) (hni : ¬Inside q C κ) :
    0 < rU p q C κ ∧ rU p q C κ ≤ C ∧ barL p q C κ = unifI 0 (rU p q C κ) ∧
      rU p q C κ = 2 * barMu p q C κ := by
  unfold Inside at hni
  have hpC : p * C = C - q * C := by rw [show p = 1 - q by linarith [h.hpq]]; ring
  have hqC : 0 < q * C := mul_pos h.hq h.hC
  unfold rU
  by_cases h1 : q * C < κ
  · have h2 : κ = C := le_antisymm h.hu (not_lt.mp fun h2 => hni ⟨h1, h2⟩)
    simp only [h1, ↓reduceIte]
    exact ⟨h.hC, le_rfl, barL_high h h2, (barMu_high h h2).symm⟩
  · have h2 : κ = q * C := le_antisymm (not_lt.mp h1) h.hl
    simp only [h1, ↓reduceIte]
    exact ⟨mul_pos h.hp h.hC, by linarith, barL_low h h2, (barMu_low h h2).symm⟩

open Classical in
/-- Part (ii) on three coordinates: `W ∼ U[0, r₀ + a]`, `U[0, r₁]` and `L̄` (Proposition 24 if
`L̄` has two steps, Lemma 18 if it is uniform). -/
def inner3 (r0a r1 p q C2 κ2 : ℝ) : SegD 3 5 :=
  if Inside q C2 κ2 then d24 r0a r1 (barMu p q C2 κ2) (C2 - κ2) C2
  else (d18 ![r0a, r1, rU p q C2 κ2]).padZ 2

/-- Part (ii) in the order `i₀, i₁, i₂, 4`: `Y_{i₀} = r₀W/(r₀ + a)`, `Y₄ = aW/(r₀ + a)`. -/
def core4 (r0 r1 a p q C2 κ2 : ℝ) : SegD 4 5 :=
  (inner3 (r0 + a) r1 p q C2 κ2).affine ![0, 1, 2, 0] ![r0 / (r0 + a), 1, 1, a / (r0 + a)]
    (fun _ => 0)

lemma good_core4 {S a r0 r1 p q C2 κ2 : ℝ} (ha : 0 ≤ a) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (h0S : r0 + a ≤ S) (h1S : r1 ≤ S) (hk : KHyp p q C2 κ2) (hCS : C2 ≤ S)
    (hmean : r0 / 2 + r1 / 2 + barMu p q C2 κ2 + a / 2 = S) :
    Good S ![unifI 0 r0, unifI 0 r1, barL p q C2 κ2, unifI 0 a] (core4 r0 r1 a p q C2 κ2) := by
  have hra : 0 < r0 + a := by linarith
  have h3 : Good S ![unifI 0 (r0 + a), unifI 0 r1, barL p q C2 κ2]
      (inner3 (r0 + a) r1 p q C2 κ2) := by
    unfold inner3
    split_ifs with hi
    · obtain ⟨m1, m2⟩ := barMu_mid hk hi.1 hi.2
      have := good_d24 (c1 := r0 + a) (c2 := r1) (μ := barMu p q C2 κ2) (a := C2 - κ2) (b := C2)
        (by linarith [hi.2]) m1 m2 (by unfold s24; linarith) (by unfold s24; linarith)
        (by unfold s24; linarith)
      refine this.congr (by unfold s24; linarith) fun j => ?_
      fin_cases j <;> simp [barL_mid hk hi.1 hi.2]
    · obtain ⟨hr2, hr2C, hbar, hrm⟩ := rU_spec hk hi
      have hsum : (∑ j, ![r0 + a, r1, rU p q C2 κ2] j) / 2 = S := by
        simp [Fin.sum_univ_three]; linarith
      have := good_d18 ![r0 + a, r1, rU p q C2 κ2]
        (fun j => by fin_cases j <;> simp <;> linarith) (by rw [hsum]; linarith)
        (fun j => by rw [hsum]; fin_cases j <;> simp <;> linarith)
      refine (this.padZ 2).congr hsum fun j => ?_
      fin_cases j <;> simp [hbar]
  have h4 := h3.affine ![0, 1, 2, 0] ![r0 / (r0 + a), 1, 1, a / (r0 + a)] (fun _ => 0) (s' := S)
    (fun x hx => by
      rw [← hx]; simp [Fin.sum_univ_four, Fin.sum_univ_three]; field_simp; ring)
  refine h4.congr rfl fun j => ?_
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [map_scale_unif (div_nonneg hr0.le hra.le) hra.le, div_mul_cancel₀ _ hra.ne']
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [map_one_zero]
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [map_scale_unif (div_nonneg ha hra.le) hra.le, div_mul_cancel₀ _ hra.ne']

open Classical in
/-- **Proposition 26 (ii)** with explicit data. -/
def iiData (C : Fin 3 → ℝ) (μ a b : ℝ) (κ : Fin 3 → ℝ) : SegD 4 5 :=
  if Inside (qw μ a b) (C 0) (κ 0) then
    (core4 (rU (pw μ a b) (qw μ a b) (C 1) (κ 1)) (rU (pw μ a b) (qw μ a b) (C 2) (κ 2)) a
      (pw μ a b) (qw μ a b) (C 0) (κ 0)).affine ![2, 0, 1, 3] (fun _ => 1) (fun _ => 0)
  else if Inside (qw μ a b) (C 1) (κ 1) then
    (core4 (rU (pw μ a b) (qw μ a b) (C 0) (κ 0)) (rU (pw μ a b) (qw μ a b) (C 2) (κ 2)) a
      (pw μ a b) (qw μ a b) (C 1) (κ 1)).affine ![0, 2, 1, 3] (fun _ => 1) (fun _ => 0)
  else
    core4 (rU (pw μ a b) (qw μ a b) (C 0) (κ 0)) (rU (pw μ a b) (qw μ a b) (C 1) (κ 1)) a
      (pw μ a b) (qw μ a b) (C 2) (κ 2)

theorem good_iiData {C : Fin 3 → ℝ} {μ a b s : ℝ} {κ : Fin 3 → ℝ} (h : Hyp C μ a b s)
    (hA : Adm C μ a b s κ) :
    Good (s - 2 * μ + a) ![bL C μ a b κ 0, bL C μ a b κ 1, bL C μ a b κ 2, unifI 0 a]
      (iiData C μ a b κ) := by
  have hk := h.khyp hA
  have hm := barMu_sum h hA
  have hCS : ∀ i, C i ≤ s - 2 * μ + a := fun i => by linarith [h.hCs i, h.ha]
  have hCS' : ∀ i, C i + a ≤ s - 2 * μ + a := fun i => by linarith [h.hCs i]
  unfold iiData
  split_ifs with h0 h1
  · obtain ⟨hr0, hr0C, he0, hrm0⟩ := rU_spec (hk 1) (hA.hone 0 1 (by decide) h0)
    obtain ⟨hr1, hr1C, he1, hrm1⟩ := rU_spec (hk 2) (hA.hone 0 2 (by decide) h0)
    have core := good_core4 h.ha hr0 hr1 (by linarith [hCS' 1]) (hr1C.trans (hCS 2))
      (hk 0) (hCS 0) (by simp only [bM] at hm; linarith)
    have := core.affine ![2, 0, 1, 3] (fun _ => 1) (fun _ => 0) (s' := s - 2 * μ + a)
      (fun x hx => by simp [Fin.sum_univ_four] at hx ⊢; linarith)
    refine this.congr rfl fun j => ?_
    fin_cases j <;> simp [bL, he0, he1, map_one_zero]
  · obtain ⟨hr0, hr0C, he0, hrm0⟩ := rU_spec (hk 0) h0
    obtain ⟨hr1, hr1C, he1, hrm1⟩ := rU_spec (hk 2) (hA.hone 1 2 (by decide) h1)
    have core := good_core4 h.ha hr0 hr1 (by linarith [hCS' 0]) (hr1C.trans (hCS 2))
      (hk 1) (hCS 1) (by simp only [bM] at hm; linarith)
    have := core.affine ![0, 2, 1, 3] (fun _ => 1) (fun _ => 0) (s' := s - 2 * μ + a)
      (fun x hx => by simp [Fin.sum_univ_four] at hx ⊢; linarith)
    refine this.congr rfl fun j => ?_
    fin_cases j <;> simp [bL, he0, he1, map_one_zero]
  · obtain ⟨hr0, hr0C, he0, hrm0⟩ := rU_spec (hk 0) h0
    obtain ⟨hr1, hr1C, he1, hrm1⟩ := rU_spec (hk 1) h1
    have core := good_core4 h.ha hr0 hr1 (by linarith [hCS' 0]) (hr1C.trans (hCS 1))
      (hk 2) (hCS 2) (by simp only [bM] at hm; linarith)
    refine core.congr rfl fun j => ?_
    fin_cases j <;> simp [bL, he0, he1]

/-- **Proposition 26** with explicit data: with probability `q` Lemma 18 for
`U[0,κ₁], U[0,κ₂], U[0,κ₃], U[0,b]`, with probability `p` the reflection of part (ii). -/
def d26 (C : Fin 3 → ℝ) (μ a b : ℝ) (κ : Fin 3 → ℝ) : SegD 4 8 :=
  (d18 ![κ 0, κ 1, κ 2, b]).app (qw μ a b)
    ((iiData C μ a b κ).affine id (fun _ => -1) ![C 0, C 1, C 2, a])

theorem good_d26 {C : Fin 3 → ℝ} {μ a b s : ℝ} {κ : Fin 3 → ℝ} (h : Hyp C μ a b s)
    (hA : Adm C μ a b s κ) :
    Good s ![unifI 0 (C 0), unifI 0 (C 1), unifI 0 (C 2), gPiece μ a b] (d26 C μ a b κ) := by
  have hk := h.khyp hA
  have hq := h.hq
  have hpq := h.hpq
  have hs0 : 0 < s := by linarith [h.s2μ, h.hb, h.ha, h.ha2]
  have hκs : ∀ i, κ i ≤ s := fun i => by linarith [hA.hu i, h.hCs i, h.ha, h.ha2]
  have hsum : (∑ j, ![κ 0, κ 1, κ 2, b] j) / 2 = s := by
    simp [Fin.sum_univ_four]; linarith [hA.hsum]
  have h1 := good_d18 ![κ 0, κ 1, κ 2, b]
    (fun j => by fin_cases j <;> simp <;> linarith [(hk 0).κpos, (hk 1).κpos, (hk 2).κpos,
      h.hb, h.ha, h.ha2]) (by rw [hsum]; exact hs0)
    (fun j => by rw [hsum]; fin_cases j <;> simp <;> linarith [hκs 0, hκs 1, hκs 2, h.hbs])
  have h1' := h1.congr hsum (F' := ![unifI 0 (κ 0), unifI 0 (κ 1), unifI 0 (κ 2), unifI 0 b])
    (fun j => by fin_cases j <;> rfl)
  have h2 := good_iiData h hA
  have h3 := h2.affine (s' := s) id (fun _ => -1) ![C 0, C 1, C 2, a] (fun x hx => by
    simp only [id, Fin.sum_univ_four, Matrix.cons_val] at hx ⊢
    linarith [h.hs])
  have h4 := h1'.app h3 hq.le (by linarith [h.hp])
  refine h4.congr rfl fun j => ?_
  fin_cases j
  · simp only [id, Fin.zero_eta, Matrix.cons_val_zero, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 0)]
  · simp only [id, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 1)]
  · simp only [id, Fin.reduceFinMk, Matrix.cons_val, bL]
    rw [reflect_barL, show 1 - qw μ a b = pw μ a b by linarith, L_split (hk 2)]
  · simp only [id, Fin.reduceFinMk, Matrix.cons_val]
    rw [reflect_unif h.ha, g_split h]

section MeasP26

variable {X : Type*} [MeasurableSpace X]

lemma measurable_rU {p q C κ : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hC : Measurable C) (hκ : Measurable κ) :
    Measurable fun x => rU (p x) (q x) (C x) (κ x) :=
  Measurable.ite (measurableSet_lt (hq.mul hC) hκ) hC (hp.mul hC)

lemma measurableSet_inside {q C κ : X → ℝ} (hq : Measurable q) (hC : Measurable C)
    (hκ : Measurable κ) : MeasurableSet {x | Inside (q x) (C x) (κ x)} :=
  (measurableSet_lt (hq.mul hC) hκ).inter (measurableSet_lt hκ hC)

lemma measurable_barMu {p q C κ : X → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hC : Measurable C) (hκ : Measurable κ) :
    Measurable fun x => barMu (p x) (q x) (C x) (κ x) := by
  unfold barMu; fun_prop

lemma measurable_inner3 {r0a r1 p q C2 κ2 : X → ℝ} (h1 : Measurable r0a) (h2 : Measurable r1)
    (hp : Measurable p) (hq : Measurable q) (hC : Measurable C2) (hκ : Measurable κ2) :
    Measurable fun x => inner3 (r0a x) (r1 x) (p x) (q x) (C2 x) (κ2 x) := by
  unfold inner3
  refine Measurable.ite (measurableSet_inside hq hC hκ)
    (measurable_d24 h1 h2 (measurable_barMu hp hq hC hκ) (hC.sub hκ) hC) ?_
  refine mPadZ (measurable_d18 fun j => ?_) 2
  fin_cases j <;> simp
  · exact h1
  · exact h2
  · exact measurable_rU hp hq hC hκ

lemma measurable_core4 {r0 r1 a p q C2 κ2 : X → ℝ} (h0 : Measurable r0) (h1 : Measurable r1)
    (ha : Measurable a) (hp : Measurable p) (hq : Measurable q) (hC : Measurable C2)
    (hκ : Measurable κ2) :
    Measurable fun x => core4 (r0 x) (r1 x) (a x) (p x) (q x) (C2 x) (κ2 x) := by
  unfold core4
  refine mAffine (measurable_inner3 (h0.add ha) h1 hp hq hC hκ) _ (fun j => ?_)
    (fun _ => measurable_const)
  fin_cases j <;> simp <;> fun_prop

lemma measurable_pw {μ a b : X → ℝ} (h1 : Measurable μ) (h2 : Measurable a)
    (h3 : Measurable b) : Measurable fun x => pw (μ x) (a x) (b x) := by unfold pw; fun_prop

lemma measurable_qw {μ a b : X → ℝ} (h1 : Measurable μ) (h2 : Measurable a)
    (h3 : Measurable b) : Measurable fun x => qw (μ x) (a x) (b x) := by unfold qw; fun_prop

lemma measurable_iiData {C : X → Fin 3 → ℝ} {μ a b : X → ℝ} {κ : X → Fin 3 → ℝ}
    (hC : ∀ i, Measurable fun x => C x i) (h1 : Measurable μ) (h2 : Measurable a)
    (h3 : Measurable b) (hκ : ∀ i, Measurable fun x => κ x i) :
    Measurable fun x => iiData (C x) (μ x) (a x) (b x) (κ x) := by
  have hp := measurable_pw h1 h2 h3
  have hq := measurable_qw h1 h2 h3
  have hr : ∀ i, Measurable fun x => rU (pw (μ x) (a x) (b x)) (qw (μ x) (a x) (b x))
      (C x i) (κ x i) := fun i => measurable_rU hp hq (hC i) (hκ i)
  unfold iiData
  refine Measurable.ite (measurableSet_inside hq (hC 0) (hκ 0)) ?_ ?_
  · exact mAffine (measurable_core4 (hr 1) (hr 2) h2 hp hq (hC 0) (hκ 0)) _
      (fun _ => measurable_const) (fun _ => measurable_const)
  refine Measurable.ite (measurableSet_inside hq (hC 1) (hκ 1)) ?_ ?_
  · exact mAffine (measurable_core4 (hr 0) (hr 2) h2 hp hq (hC 1) (hκ 1)) _
      (fun _ => measurable_const) (fun _ => measurable_const)
  · exact measurable_core4 (hr 0) (hr 1) h2 hp hq (hC 2) (hκ 2)

lemma measurable_d26 {C : X → Fin 3 → ℝ} {μ a b : X → ℝ} {κ : X → Fin 3 → ℝ}
    (hC : ∀ i, Measurable fun x => C x i) (h1 : Measurable μ) (h2 : Measurable a)
    (h3 : Measurable b) (hκ : ∀ i, Measurable fun x => κ x i) :
    Measurable fun x => d26 (C x) (μ x) (a x) (b x) (κ x) := by
  unfold d26
  refine mApp (measurable_d18 fun j => ?_) (mAffine (measurable_iiData hC h1 h2 h3 hκ) _
    (fun _ => measurable_const) (fun j => ?_)) (measurable_qw h1 h2 h3)
  · fin_cases j <;> simp
    · exact hκ 0
    · exact hκ 1
    · exact hκ 2
    · exact h3
  · fin_cases j <;> simp
    · exact hC 0
    · exact hC 1
    · exact hC 2
    · exact h2

lemma measurable_kGreedy {C : X → Fin 3 → ℝ} {μ a b s : X → ℝ}
    (hC : ∀ i, Measurable fun x => C x i) (h1 : Measurable μ) (h2 : Measurable a)
    (h3 : Measurable b) (h4 : Measurable s) (i : Fin 3) :
    Measurable fun x => kGreedy (C x) (μ x) (a x) (b x) (s x) i := by
  have hp := measurable_pw h1 h2 h3
  have hq := measurable_qw h1 h2 h3
  have := hC 0; have := hC 1; have := hC 2
  fin_cases i <;> simp [kGreedy] <;> fun_prop

end MeasP26

/-! ### Leaves: grouping and lifting (the paragraph before Proposition 26) -/

/-- The totals of the groups `G` over the coordinates other than `k`. -/
def gTot {m : ℕ} (v : Fin n → ℝ) (k : Fin n) (G : Fin n → Fin m) (i : Fin m) : ℝ :=
  ∑ j, if j ≠ k ∧ G j = i then v j else 0

/-- The index map of the lift: `k` goes to the coordinate `pk` of the two-step distribution,
the other coordinates to their groups. -/
def lσ {m : ℕ} (k : Fin n) (G : Fin n → Fin m) (pk : Fin m) (j : Fin n) : Fin m :=
  if j = k then pk else G j

/-- The coefficients of the lift. -/
def lc {m : ℕ} (v : Fin n → ℝ) (k : Fin n) (G : Fin n → Fin m) (j : Fin n) : ℝ :=
  if j = k then 1 else v j / gTot v k G (G j)

lemma sum_fiber_eq {m : ℕ} (σ : Fin n → Fin m) (c : Fin n → ℝ)
    (h : ∀ i, ∑ j, (if σ j = i then c j else 0) = 1) (x : Fin m → ℝ) :
    ∑ j, c j * x (σ j) = ∑ i, x i := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j ∈ Finset.univ.filter (fun j => σ j = i), c j * x (σ j) = c j * x i := by
    intro j hj; rw [(Finset.mem_filter.mp hj).2]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, Finset.sum_filter, h i, one_mul]

lemma fiber_lc {m : ℕ} (v : Fin n → ℝ) (k : Fin n) (G : Fin n → Fin m) (pk : Fin m)
    (i : Fin m) : ∑ j, (if lσ k G pk j = i then lc v k G j else 0) =
      (if pk = i then 1 else 0) + gTot v k G i / gTot v k G i := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  simp only [lσ, lc, ↓reduceIte]
  congr 1
  rw [gTot, Finset.sum_div, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_div, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≠ k := Finset.ne_of_mem_erase hj
  simp only [hjk, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
  split_ifs with h1 <;> simp [h1, gTot]

/-- The lift of group data to a leaf: coordinate `k` is the two-step coordinate `pk`, every
other coordinate `j` is `v_j / C_{G j}` times its group coordinate. -/
lemma good_leaf_lift {m : ℕ} {s : ℝ} {d : SegD m K} {F : Fin m → Measure ℝ} (hd : Good s F d)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (k : Fin n) (G : Fin n → Fin m) (pk : Fin m)
    (hF : ∀ i, i ≠ pk → F i = unifI 0 (gTot v k G i)) (hFp : ∀ i, IsProbabilityMeasure (F i))
    (hpk : gTot v k G pk = 0) (hpos : ∀ i, i ≠ pk → gTot v k G i ≠ 0) :
    Good s (fun j => if j = k then F pk else unifI 0 (v j))
      (d.affine (lσ k G pk) (lc v k G) (fun _ => 0)) := by
  classical
  have hfib : ∀ i, ∑ j, (if lσ k G pk j = i then lc v k G j else 0) = 1 := by
    intro i
    rw [fiber_lc]
    by_cases hi : pk = i
    · subst hi; simp [hpk]
    · simp [hi, div_self (hpos i (Ne.symm hi))]
  have h := hd.affine (lσ k G pk) (lc v k G) (fun _ => 0) (s' := s) (fun x hx => by
    simp only [add_zero]; rw [sum_fiber_eq _ _ hfib, hx])
  refine h.congr rfl fun j => ?_
  simp only [add_zero]
  by_cases hjk : j = k
  · subst hjk; simp [lσ, lc]
  · simp only [lσ, lc, hjk, ↓reduceIte]
    have hle : v j ≤ gTot v k G (G j) := by
      have := Finset.single_le_sum (f := fun j' => if j' ≠ k ∧ G j' = G j then v j' else 0)
        (fun j' _ => by split_ifs <;> simp [hv]) (Finset.mem_univ j)
      simpa [gTot, hjk] using this
    by_cases h0 : gTot v k G (G j) = 0
    · have hv0 : v j = 0 := le_antisymm (h0 ▸ hle) (hv j)
      rw [h0, hv0, zero_div]
      have : (fun x : ℝ => 0 * x) = fun _ => 0 := by funext x; ring
      rw [this, Measure.map_const, measure_univ, one_smul, unifI_self]
    · have hGj : G j ≠ pk := fun h => h0 (h ▸ hpk)
      rw [hF _ hGj]
      have hC0 : 0 ≤ gTot v k G (G j) := le_trans (hv j) hle
      have := map_scale_unif (div_nonneg (hv j) hC0) hC0
      simp only [add_zero] at this
      rw [this, div_mul_cancel₀ _ h0]

lemma gTot_comp {m m' : ℕ} (v : Fin n → ℝ) (k : Fin n) (G : Fin n → Fin m)
    (f : Fin m → Fin m') (i : Fin m') :
    gTot v k (fun j => f (G j)) i = ∑ i', if f i' = i then gTot v k G i' else 0 := by
  classical
  unfold gTot
  have e : ∀ i', (if f i' = i then ∑ j, (if j ≠ k ∧ G j = i' then v j else 0) else 0) =
      ∑ j, (if f i' = i ∧ j ≠ k ∧ G j = i' then v j else 0) := by
    intro i'; split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl (fun i' _ => e i'), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (G j)]
  · by_cases h1 : j ≠ k <;> by_cases h2 : f (G j) = i <;> simp [h1, h2]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma gTot_sum {m : ℕ} (v : Fin n → ℝ) (k : Fin n) (G : Fin n → Fin m) :
    ∑ i, gTot v k G i = ∑ j, v j - v k := by
  classical
  unfold gTot
  rw [Finset.sum_comm]
  have e : ∀ j, ∑ i, (if j ≠ k ∧ G j = i then v j else 0) = v j - if j = k then v j else 0 := by
    intro j
    by_cases hj : j = k
    · simp [hj]
    · simp [hj]
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

/-- The group totals of the cut of `v` at `(∑ v)/2` (Lemma 18), without coordinate `k`. -/
def C0 (v : Fin n → ℝ) (k : Fin n) : Fin 3 → ℝ := gTot v k (g18 v)

/-- Two of the three groups can be merged (their totals add up to at most `s`). -/
def Two (C : Fin 3 → ℝ) (s : ℝ) : Prop := C 0 + C 1 ≤ s ∨ C 0 + C 2 ≤ s ∨ C 1 + C 2 ≤ s

/-- The merging of two groups (identity if no two groups can be merged). -/
def mm (C : Fin 3 → ℝ) (s : ℝ) : Fin 3 → Fin 3 :=
  if C 0 + C 1 ≤ s then ![0, 0, 1] else if C 0 + C 2 ≤ s then ![0, 1, 0]
  else if C 1 + C 2 ≤ s then ![0, 1, 1] else ![0, 1, 2]

/-- The grouping of a leaf: the cut of Lemma 18, followed by the merging. -/
def lG (v : Fin n → ℝ) (k : Fin n) (j : Fin n) : Fin 3 :=
  mm (C0 v k) ((∑ j, v j) / 2) (g18 v j)

/-- The castSucc of the grouping (group coordinates `0, 1, 2` of Proposition 26). -/
def lG4 (v : Fin n → ℝ) (k : Fin n) (j : Fin n) : Fin 4 := (lG v k j).castSucc

open Classical in
/-- The data of a leaf whose coordinate `k` has two steps: Proposition 24 for two groups,
Proposition 26 for three groups. -/
def leafK (a b v : Fin n → ℝ) (k : Fin n) : SegD n 8 :=
  if Two (C0 v k) ((∑ j, v j) / 2) then
    ((d24 (gTot v k (lG v k) 0) (gTot v k (lG v k) 1) (v k / 2) (a k) (b k)).affine
      (lσ k (lG v k) 2) (lc v k (lG v k)) (fun _ => 0)).padZ 3
  else
    (d26 (gTot v k (lG v k)) (v k / 2) (a k) (b k)
      (kGreedy (gTot v k (lG v k)) (v k / 2) (a k) (b k) ((∑ j, v j) / 2))).affine
      (lσ k (lG4 v k) 3) (lc v k (lG4 v k)) (fun _ => 0)

lemma vec012 (i : Fin 3) : (![0, 1, 2] : Fin 3 → Fin 3) i = i := by fin_cases i <;> rfl

theorem good_leafK {a b v : Fin n → ℝ} {k : Fin n} (hvn : ∀ j, 0 ≤ v j)
    (hvs : ∀ j, v j ≤ (∑ j, v j) / 2) (ha : 0 ≤ a k) (hak : a k < v k) (hkb : v k < b k)
    (hbs : b k ≤ (∑ j, v j) / 2) :
    Good ((∑ j, v j) / 2) (fun j => if j = k then gPiece (v k / 2) (a k) (b k)
      else unifI 0 (v j)) (leafK a b v k) := by
  classical
  set s := (∑ j, v j) / 2 with hsdef
  have hsum : ∑ j, v j = 2 * s := by rw [hsdef]; ring
  have hs0 : 0 ≤ s := le_trans (hvn k) (hvs k)
  set C := C0 v k with hCdef
  have hCle : ∀ i, C i ≤ s := fun i => by
    have := L18.group_sum_le v hvn hsum hs0 hvs i
    refine le_trans ?_ this
    simp only [hCdef, C0, gTot]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h1 : j ≠ k ∧ g18 v j = i
    · have h2 : L18.grp (L18.ext v) s j.val = i := h1.2
      simp [h1, h2]
    · simp only [h1, ↓reduceIte]; split_ifs <;> simp [hvn]
  have hCnn : ∀ i, 0 ≤ C i := fun i => by
    simp only [hCdef, C0, gTot]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hvn]
  have hCsum : C 0 + C 1 + C 2 = 2 * s - v k := by
    have := gTot_sum v k (g18 v)
    rw [Fin.sum_univ_three] at this
    simp only [hCdef, C0]; rw [this, hsum]
  have hCf : ∀ i, gTot v k (lG v k) i = ∑ i', if mm C s i' = i then C i' else 0 := fun i =>
    gTot_comp v k (g18 v) (mm C s) i
  have hμ : 2 * (v k / 2) = v k := by ring
  unfold leafK
  rw [← hCdef]
  split_ifs with htwo
  · -- two groups
    rw [← hsdef] at htwo
    obtain ⟨c1, c2, e0, e1, h1, h0, hle0, hle1⟩ : ∃ c1 c2, gTot v k (lG v k) 0 = c1 ∧
        gTot v k (lG v k) 1 = c2 ∧ gTot v k (lG v k) 2 = 0 ∧ c1 + c2 = 2 * s - v k ∧
        c1 ≤ s ∧ c2 ≤ s := by
      by_cases h01 : C 0 + C 1 ≤ s
      · refine ⟨C 0 + C 1, C 2, ?_, ?_, ?_, by linarith, h01, hCle 2⟩ <;>
          rw [hCf] <;> simp [Fin.sum_univ_three, mm, h01]
      by_cases h02 : C 0 + C 2 ≤ s
      · refine ⟨C 0 + C 2, C 1, ?_, ?_, ?_, by linarith, h02, hCle 1⟩ <;>
          rw [hCf] <;> simp [Fin.sum_univ_three, mm, h01, h02]
      have h12 : C 1 + C 2 ≤ s := by
        rcases htwo with h | h | h
        · exact absurd h h01
        · exact absurd h h02
        · exact h
      · refine ⟨C 0, C 1 + C 2, ?_, ?_, ?_, by linarith, hCle 0, h12⟩ <;>
          rw [hCf] <;> simp [Fin.sum_univ_three, mm, h01, h02, h12]
    have hp0 : 0 < c1 := by linarith
    have hp1 : 0 < c2 := by linarith
    have hd := good_d24 (c1 := c1) (c2 := c2) (μ := v k / 2)
      (a := a k) (b := b k) ha (by linarith) (by linarith) (by unfold s24; linarith)
      (by unfold s24; linarith) (by unfold s24; linarith)
    have hs24 : s24 c1 c2 (v k / 2) = s := by
      unfold s24; linarith
    rw [hs24, ← e0, ← e1] at hd
    have hl := good_leaf_lift hd v hvn k (lG v k) 2 (fun i hi => by
        fin_cases i
        · rfl
        · rfl
        · exact absurd rfl hi)
      (fun i => by
        fin_cases i
        · exact unifI_isProb _ _
        · exact unifI_isProb _ _
        · exact gPiece_isProb (by linarith) (by linarith))
      h1 (fun i hi => by
        fin_cases i
        · simp only [Fin.zero_eta, e0]; exact hp0.ne'
        · simp only [Fin.mk_one, e1]; exact hp1.ne'
        · exact absurd rfl hi)
    refine (hl.padZ 3).congr rfl fun j => ?_
    by_cases hj : j = k <;> simp [hj]
  · -- three groups
    rw [← hsdef] at htwo
    have hid : ∀ i, mm C s i = i := fun i => by
      simp only [Two, not_or, not_le] at htwo
      simp only [mm, not_le.mpr htwo.1, not_le.mpr htwo.2.1, not_le.mpr htwo.2.2, ↓reduceIte,
        vec012]
    have hCf' : ∀ i, gTot v k (lG v k) i = C i := fun i => by
      rw [hCf]; simp [hid]
    simp only [Two, not_or, not_le] at htwo
    obtain ⟨t01, t02, t12⟩ := htwo
    have hCi : ∀ i, C i < s - v k := fun i => by
      fin_cases i <;> simp <;> linarith
    have hCp : ∀ i, 0 < C i := fun i => by
      fin_cases i <;> simp <;> linarith [hCi 0, hCi 1, hCi 2]
    have hyp : Hyp (gTot v k (lG v k)) (v k / 2) (a k) (b k) s := by
      refine ⟨fun i => by rw [hCf']; exact hCp i, ha, by linarith, by linarith, ?_, hbs,
        fun i => by rw [hCf']; linarith [hCi i]⟩
      rw [hCf', hCf', hCf']; linarith
    have hd := good_d26 hyp (prop26_kappa hyp)
    have hG4 : ∀ i : Fin 3, gTot v k (lG4 v k) i.castSucc = gTot v k (lG v k) i := fun i => by
      unfold gTot lG4
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Fin.castSucc_inj]
    have hG43 : gTot v k (lG4 v k) 3 = 0 := by
      unfold gTot lG4
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (lG v k j).castSucc ≠ 3 := fun h => by
        have := Fin.castSucc_lt_last (lG v k j)
        rw [h] at this; exact absurd this (lt_irrefl _)
      simp [this]
    have hl := good_leaf_lift hd v hvn k (lG4 v k) 3 (fun i hi => by
        fin_cases i
        · exact congrArg (unifI 0) (hG4 0).symm
        · exact congrArg (unifI 0) (hG4 1).symm
        · exact congrArg (unifI 0) (hG4 2).symm
        · exact absurd rfl hi)
      (fun i => by
        fin_cases i
        · exact unifI_isProb _ _
        · exact unifI_isProb _ _
        · exact unifI_isProb _ _
        · exact gPiece_isProb (by linarith) (by linarith))
      hG43 (fun i hi => by
        fin_cases i
        · rw [show (⟨0, by omega⟩ : Fin 4) = (0 : Fin 3).castSucc from rfl, hG4, hCf']
          exact (hCp 0).ne'
        · rw [show (⟨1, by omega⟩ : Fin 4) = (1 : Fin 3).castSucc from rfl, hG4, hCf']
          exact (hCp 1).ne'
        · rw [show (⟨2, by omega⟩ : Fin 4) = (2 : Fin 3).castSucc from rfl, hG4, hCf']
          exact (hCp 2).ne'
        · exact absurd rfl hi)
    refine hl.congr rfl fun j => ?_
    by_cases hj : j = k <;> simp [hj]

section MeasLeaf

variable {X : Type*} [MeasurableSpace X]

lemma measurable_gTot {m : ℕ} {v : X → Fin n → ℝ} (hv : ∀ j, Measurable fun x => v x j)
    {G : X → Fin n → Fin m} (hG : ∀ j, Measurable fun x => G x j) (k : Fin n) (i : Fin m) :
    Measurable fun x => gTot (v x) k (G x) i := by
  unfold gTot
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases hj : j = k
  · simp only [hj, ne_eq, not_true_eq_false, false_and, ↓reduceIte]; exact measurable_const
  · simp only [ne_eq, hj, not_false_eq_true, true_and]
    exact Measurable.ite (measurableSet_eq_fun (hG j) measurable_const) (hv j) measurable_const

lemma measurable_g18 {v : X → Fin n → ℝ} (hv : ∀ j, Measurable fun x => v x j) (j : Fin n) :
    Measurable fun x => g18 (v x) j :=
  measurable_grp hv ((Finset.measurable_sum _ fun j _ => hv j).div_const _) j.val

lemma mm_apply (C : Fin 3 → ℝ) (s : ℝ) (i : Fin 3) : mm C s i =
    if C 0 + C 1 ≤ s then ![0, 0, 1] i else if C 0 + C 2 ≤ s then ![0, 1, 0] i
    else if C 1 + C 2 ≤ s then ![0, 1, 1] i else ![0, 1, 2] i := by
  unfold mm; split_ifs <;> rfl

lemma measurable_lG {v : X → Fin n → ℝ} (hv : ∀ j, Measurable fun x => v x j) (k j : Fin n) :
    Measurable fun x => lG (v x) k j := by
  have hC : ∀ i, Measurable fun x => C0 (v x) k i := fun i =>
    measurable_gTot hv (measurable_g18 hv) k i
  have hs : Measurable fun x => (∑ j, v x j) / 2 :=
    (Finset.measurable_sum _ fun j _ => hv j).div_const _
  unfold lG
  refine measurable_comp_fin (F := fun x i => mm (C0 (v x) k) ((∑ j, v x j) / 2) i)
    (measurable_g18 hv j) fun i => ?_
  simp_rw [mm_apply]
  exact Measurable.ite (measurableSet_le ((hC 0).add (hC 1)) hs) measurable_const
    (Measurable.ite (measurableSet_le ((hC 0).add (hC 2)) hs) measurable_const
      (Measurable.ite (measurableSet_le ((hC 1).add (hC 2)) hs) measurable_const
        measurable_const))

lemma measurable_lG4 {v : X → Fin n → ℝ} (hv : ∀ j, Measurable fun x => v x j) (k j : Fin n) :
    Measurable fun x => lG4 (v x) k j :=
  (Measurable.of_discrete (f := (Fin.castSucc : Fin 3 → Fin 4))).comp (measurable_lG hv k j)

lemma measurable_lσ {m : ℕ} {G : X → Fin n → Fin m} (hG : ∀ j, Measurable fun x => G x j)
    (k : Fin n) (pk : Fin m) (j : Fin n) : Measurable fun x => lσ k (G x) pk j := by
  unfold lσ
  by_cases hj : j = k
  · simp only [hj, ↓reduceIte]; exact measurable_const
  · simp only [hj, ↓reduceIte]; exact hG j

lemma measurable_lc {m : ℕ} {v : X → Fin n → ℝ} (hv : ∀ j, Measurable fun x => v x j)
    {G : X → Fin n → Fin m} (hG : ∀ j, Measurable fun x => G x j) (k j : Fin n) :
    Measurable fun x => lc (v x) k (G x) j := by
  unfold lc
  by_cases hj : j = k
  · simp only [hj, ↓reduceIte]; exact measurable_const
  · simp only [hj, ↓reduceIte]
    exact measurable_comp_fin (F := fun x i => v x j / gTot (v x) k (G x) i) (hG j)
      fun i => (hv j).div (measurable_gTot hv hG k i)

lemma measurable_leafK {a b v : X → Fin n → ℝ} (ha : ∀ j, Measurable fun x => a x j)
    (hb : ∀ j, Measurable fun x => b x j) (hv : ∀ j, Measurable fun x => v x j) (k : Fin n) :
    Measurable fun x => leafK (a x) (b x) (v x) k := by
  have hC : ∀ i, Measurable fun x => C0 (v x) k i := fun i =>
    measurable_gTot hv (measurable_g18 hv) k i
  have hs : Measurable fun x => (∑ j, v x j) / 2 :=
    (Finset.measurable_sum _ fun j _ => hv j).div_const _
  have hG := measurable_lG hv k
  have hG4 := measurable_lG4 hv k
  have hT : ∀ i, Measurable fun x => gTot (v x) k (lG (v x) k) i := measurable_gTot hv hG k
  have hμ : Measurable fun x => v x k / 2 := (hv k).div_const _
  unfold leafK
  refine Measurable.ite ?_ ?_ ?_
  · exact ((measurableSet_le ((hC 0).add (hC 1)) hs).union
      ((measurableSet_le ((hC 0).add (hC 2)) hs).union
        (measurableSet_le ((hC 1).add (hC 2)) hs)))
  · exact mPadZ (mAffineVar (measurable_d24 (hT 0) (hT 1) hμ (ha k) (hb k))
      (measurable_lσ hG k 2) (measurable_lc hv hG k) fun _ => measurable_const) 3
  · exact mAffineVar (measurable_d26 hT hμ (ha k) (hb k)
      (measurable_kGreedy hT hμ (ha k) (hb k) hs)) (measurable_lσ hG4 k 3)
      (measurable_lc hv hG4 k) fun _ => measurable_const

end MeasLeaf

open Classical in
/-- The data of a leaf of Lemma 23: Lemma 18 if no coordinate lies strictly inside its
interval, otherwise `leafK` for that coordinate (the first one, in a fixed order). -/
def leafD (a b v : Fin n → ℝ) : SegD n 8 :=
  (List.finRange n).foldr (fun k acc => if a k < v k ∧ v k < b k then leafK a b v k else acc)
    ((d18 v).padZ 5)

lemma foldr_none {α β : Type*} (P : α → Prop) [DecidablePred P] (f : α → β) (d : β)
    (L : List α) (h : ∀ j ∈ L, ¬P j) :
    L.foldr (fun k acc => if P k then f k else acc) d = d := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.foldr_cons, h j (by simp), ↓reduceIte]
    exact ih fun j' hj' => h j' (by simp [hj'])

lemma foldr_one {α β : Type*} (P : α → Prop) [DecidablePred P] (f : α → β) (d : β)
    (L : List α) {k : α} (hk : P k) (huniq : ∀ j, P j → j = k) (hkL : k ∈ L) :
    L.foldr (fun k acc => if P k then f k else acc) d = f k := by
  induction L with
  | nil => simp at hkL
  | cons j L ih =>
    simp only [List.foldr_cons]
    by_cases hj : P j
    · obtain rfl := huniq j hj; simp [hj]
    · simp only [hj, ↓reduceIte]
      refine ih ?_
      rcases List.mem_cons.mp hkL with h | h
      · exact absurd (h ▸ hk) hj
      · exact h

lemma phi_end {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (hni : ¬(a < x ∧ x < b)) :
    phi a b x = unifI 0 x := by
  unfold phi
  rw [ite_eq_left_iff.mpr]
  intro h
  exfalso
  push Not at h
  exact hni ⟨lt_of_le_of_ne hx.1 (Ne.symm h.1), lt_of_le_of_ne hx.2 h.2⟩

lemma phi_inner {a b x : ℝ} (hx : a < x ∧ x < b) : phi a b x = gPiece (x / 2) a b := by
  unfold phi
  rw [ite_eq_right_iff.mpr]
  rintro (h | h) <;> linarith [hx.1, hx.2]

/-- **A leaf of Lemma 23** (`j:lem:split`): if every coordinate lies in its interval
`[a_j, b_j]`, at most one strictly inside, `a ≥ 0`, `b_j ≤ s = (∑ v)/2` and `s > 0`, then
`leafD a b v` is a mixture of at most eight uniform distributions on segments in `H_s` that is a
joint mix of the leaf `φ_1(v_1), …, φ_n(v_n)`. -/
theorem good_leafD {a b v : Fin n → ℝ} (hbox : ∀ j, a j ≤ v j ∧ v j ≤ b j)
    (hone : (JointLemmas.inner a b v).card ≤ 1) (ha : ∀ j, 0 ≤ a j)
    (hbs : ∀ j, b j ≤ (∑ j, v j) / 2)
    (hs : 0 < (∑ j, v j) / 2) :
    Good ((∑ j, v j) / 2) (fun j => phi (a j) (b j) (v j)) (leafD a b v) := by
  classical
  have hvn : ∀ j, 0 ≤ v j := fun j => le_trans (ha j) (hbox j).1
  have hvs : ∀ j, v j ≤ (∑ j, v j) / 2 := fun j => le_trans (hbox j).2 (hbs j)
  unfold leafD
  by_cases hex : ∃ k, a k < v k ∧ v k < b k
  · obtain ⟨k, hk⟩ := hex
    have huniq : ∀ j, (a j < v j ∧ v j < b j) → j = k := by
      intro j hj
      by_contra hne
      have h2 : ({j, k} : Finset (Fin n)) ⊆ JointLemmas.inner a b v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [JointLemmas.inner, hj, hk]
      have := Finset.card_le_card h2
      rw [Finset.card_pair hne] at this
      omega
    rw [foldr_one (fun k => a k < v k ∧ v k < b k) _ _ _ hk huniq (List.mem_finRange k)]
    refine (good_leafK hvn hvs (ha k) hk.1 hk.2 (hbs k)).congr rfl fun j => ?_
    by_cases hjk : j = k
    · subst hjk; simp [phi_inner hk]
    · simp only [hjk, ↓reduceIte]
      exact (phi_end (hbox j) fun h => hjk (huniq j h)).symm
  · push Not at hex
    rw [foldr_none (fun k => a k < v k ∧ v k < b k) _ _ _ fun j _ h => by
      linarith [hex j h.1, h.2]]
    refine ((good_d18 v hvn hs hvs).padZ 5).congr rfl fun j => ?_
    exact (phi_end (hbox j) fun h => by linarith [hex j h.1, h.2]).symm

lemma measurable_leafD {X : Type*} [MeasurableSpace X] {a b v : X → Fin n → ℝ}
    (ha : ∀ j, Measurable fun x => a x j) (hb : ∀ j, Measurable fun x => b x j)
    (hv : ∀ j, Measurable fun x => v x j) : Measurable fun x => leafD (a x) (b x) (v x) := by
  classical
  unfold leafD
  induction (List.finRange n) with
  | nil => exact mPadZ (measurable_d18 hv) 5
  | cons k L ih =>
    simp only [List.foldr_cons]
    exact Measurable.ite ((measurableSet_lt (ha k) (hv k)).inter (measurableSet_lt (hv k) (hb k)))
      (measurable_leafK ha hb hv k) ih

/-! ### The mixture over the leaves (Lemma 23), measurable in the pieces -/

/-- The joint mix of a leaf. -/
def leafM (a b v : Fin n → ℝ) : Measure (Fin n → ℝ) := (leafD a b v).mix

/-- The mixture of the leaf joint mixes over the outputs of the procedure of Lemma 23. -/
def procMix (μ a b : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  ((proc a b n (fun j => 2 * μ j) 1).map fun p => ENNReal.ofReal p.2 • leafM a b p.1).sum

/-- **Lemma 23 with the leaves**: for pieces `(a_j, b_j)` for the means `μ_j ≥ 0`, with
`b_j ≤ s = ∑ μ_j` and `s > 0`, `procMix μ a b` is a joint mix of the pieces with sum `s`. -/
theorem procMix_spec {μ a b : Fin n → ℝ} (hp : ∀ j, IsPiece (μ j) (a j) (b j))
    (hμ : ∀ j, 0 ≤ μ j) (hbs : ∀ j, b j ≤ ∑ j, μ j) (hs : 0 < ∑ j, μ j) :
    IsJointMix (fun j => piece (μ j) (a j) (b j)) (procMix μ a b) ∧
      ∀ᵐ x ∂procMix μ a b, ∑ j, x j = ∑ j, μ j := by
  have ha : ∀ j, 0 ≤ a j := fun j => by
    rcases hp j with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · rw [h]; linarith [hμ j]
  obtain ⟨-, hout, -, -, hmix⟩ := split_lemma hp
  refine hmix (fun v => leafM a b v) fun p hp' => ?_
  obtain ⟨-, hsum, hbox, hone⟩ := hout p hp'
  have e : (∑ j, p.1 j) / 2 = ∑ j, μ j := by rw [hsum]; ring
  have hg := good_leafD hbox hone ha (fun j => e ▸ hbs j) (e ▸ hs)
  rw [e] at hg
  exact hg.joint

section MeasProc

variable {X : Type*} [MeasurableSpace X]

local instance : MeasurableSpace (Finset (Fin n)) := ⊤
local instance : DiscreteMeasurableSpace (Finset (Fin n)) := ⟨fun _ => trivial⟩

lemma measurable_measure_add {μ ν : X → Measure (Fin n → ℝ)} (hμ : Measurable μ)
    (hν : Measurable ν) : Measurable fun x => μ x + ν x :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [add_apply]
    exact (Measure.measurable_coe hs).comp hμ |>.add ((Measure.measurable_coe hs).comp hν)

lemma measurable_measure_smul {c : X → ℝ} (hc : Measurable c) {μ : X → Measure (Fin n → ℝ)}
    (hμ : Measurable μ) : Measurable fun x => ENNReal.ofReal (c x) • μ x :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [smul_apply, smul_eq_mul]
    exact (ENNReal.measurable_ofReal.comp hc).mul ((Measure.measurable_coe hs).comp hμ)

lemma measurable_inner {a b v : X → Fin n → ℝ} (ha : ∀ j, Measurable fun x => a x j)
    (hb : ∀ j, Measurable fun x => b x j) (hv : ∀ j, Measurable fun x => v x j) :
    Measurable fun x => JointLemmas.inner (a x) (b x) (v x) := by
  refine measurable_to_countable' fun S => ?_
  have e : (fun x => JointLemmas.inner (a x) (b x) (v x)) ⁻¹' {S} =
      ⋂ j, {x | (a x j < v x j ∧ v x j < b x j) ↔ j ∈ S} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq, Finset.ext_iff,
      JointLemmas.inner, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e]
  refine MeasurableSet.iInter fun j => ?_
  have hm : MeasurableSet {x | a x j < v x j ∧ v x j < b x j} :=
    (measurableSet_lt (ha j) (hv j)).inter (measurableSet_lt (hv j) (hb j))
  by_cases hj : j ∈ S
  · convert hm using 1; ext x; simp [hj]
  · convert hm.compl using 1; ext x; simp [hj]

/-- The mixture of `L` over the outputs of the procedure. -/
def procSum (L : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Measure (Fin n → ℝ))
    (A B : Fin n → ℝ) (fuel : ℕ) (V : Fin n → ℝ) (Θ : ℝ) : Measure (Fin n → ℝ) :=
  ((proc A B fuel V Θ).map fun p => ENNReal.ofReal p.2 • L (A, B, p.1)).sum

/-- The step sizes of the procedure. -/
def tpF (A B V : Fin n → ℝ) (i k : Fin n) : ℝ := min (B i - V i) (V k - A k)

/-- The step sizes of the procedure. -/
def tmF (A B V : Fin n → ℝ) (i k : Fin n) : ℝ := min (V i - A i) (B k - V k)

lemma procSum_succ (L : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Measure (Fin n → ℝ))
    (A B : Fin n → ℝ) (fuel : ℕ) (V : Fin n → ℝ) (Θ : ℝ) :
    procSum L A B (fuel + 1) V Θ =
      if h : 2 ≤ (JointLemmas.inner A B V).card then
        procSum L A B fuel
            (V + tpF A B V (first _ h) (second _ h) • dir (first _ h) (second _ h))
            (Θ * tmF A B V (first _ h) (second _ h) /
              (tpF A B V (first _ h) (second _ h) + tmF A B V (first _ h) (second _ h))) +
          procSum L A B fuel
            (V - tmF A B V (first _ h) (second _ h) • dir (first _ h) (second _ h))
            (Θ * tpF A B V (first _ h) (second _ h) /
              (tpF A B V (first _ h) (second _ h) + tmF A B V (first _ h) (second _ h)))
      else ENNReal.ofReal Θ • L (A, B, V) := by
  unfold procSum
  rw [proc]
  split_ifs with h
  · rw [List.map_append, List.sum_append]; rfl
  · simp

/-- The mixture over the outputs of the procedure is measurable in the input. -/
lemma measurable_procSum (L : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Measure (Fin n → ℝ))
    (hL : Measurable L) (fuel : ℕ) {A B V : X → Fin n → ℝ} {Θ : X → ℝ}
    (hA : ∀ j, Measurable fun x => A x j) (hB : ∀ j, Measurable fun x => B x j)
    (hV : ∀ j, Measurable fun x => V x j) (hΘ : Measurable Θ) :
    Measurable fun x => procSum L (A x) (B x) fuel (V x) (Θ x) := by
  have hLc : ∀ {V : X → Fin n → ℝ}, (∀ j, Measurable fun x => V x j) →
      Measurable fun x => L (A x, B x, V x) := fun hV =>
    hL.comp ((measurable_pi_iff.mpr hA).prodMk
      ((measurable_pi_iff.mpr hB).prodMk (measurable_pi_iff.mpr hV)))
  induction fuel generalizing V Θ with
  | zero =>
    simp only [procSum, proc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    exact measurable_measure_smul hΘ (hLc hV)
  | succ fuel ih =>
    let Ψ : Fin n → Fin n → X → Measure (Fin n → ℝ) := fun i k x =>
      procSum L (A x) (B x) fuel (V x + tpF (A x) (B x) (V x) i k • dir i k)
          (Θ x * tmF (A x) (B x) (V x) i k /
            (tpF (A x) (B x) (V x) i k + tmF (A x) (B x) (V x) i k)) +
        procSum L (A x) (B x) fuel (V x - tmF (A x) (B x) (V x) i k • dir i k)
          (Θ x * tpF (A x) (B x) (V x) i k /
            (tpF (A x) (B x) (V x) i k + tmF (A x) (B x) (V x) i k))
    have hΨ : ∀ i k, Measurable (Ψ i k) := fun i k => by
      have htp : Measurable fun x => tpF (A x) (B x) (V x) i k :=
        ((hB i).sub (hV i)).min ((hV k).sub (hA k))
      have htm : Measurable fun x => tmF (A x) (B x) (V x) i k :=
        ((hV i).sub (hA i)).min ((hB k).sub (hV k))
      refine measurable_measure_add (ih (fun j => ?_) ?_) (ih (fun j => ?_) ?_)
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact (hV j).add (htp.mul_const _)
      · exact (hΘ.mul htm).div (htp.add htm)
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact (hV j).sub (htm.mul_const _)
      · exact (hΘ.mul htp).div (htp.add htm)
    let Φ : X × Finset (Fin n) → Measure (Fin n → ℝ) := fun z =>
      if h : 2 ≤ z.2.card then Ψ (first z.2 h) (second z.2 h) z.1
      else ENNReal.ofReal (Θ z.1) • L (A z.1, B z.1, V z.1)
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left fun S => ?_
      by_cases h : 2 ≤ S.card
      · have e : (fun x => Φ (x, S)) = Ψ (first S h) (second S h) :=
          funext fun x => dite_eq_left h
        rw [e]
        exact hΨ _ _
      · have e : (fun x => Φ (x, S)) = fun x => ENNReal.ofReal (Θ x) • L (A x, B x, V x) :=
          funext fun x => dite_eq_right h
        rw [e]
        exact measurable_measure_smul hΘ (hLc hV)
    have e : (fun x => procSum L (A x) (B x) (fuel + 1) (V x) (Θ x)) =
        fun x => Φ (x, JointLemmas.inner (A x) (B x) (V x)) := by
      funext x
      exact procSum_succ L (A x) (B x) fuel (V x) (Θ x)
    rw [e]
    exact hΦ.comp (measurable_id.prodMk (measurable_inner hA hB hV))

end MeasProc

lemma measurable_leafM :
    Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => leafM z.1 z.2.1 z.2.2 :=
  measurable_segMix.comp (measurable_leafD (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)))

/-- `procMix` is measurable in the means and the pieces. -/
theorem measurable_procMix {X : Type*} [MeasurableSpace X] {μ a b : X → Fin n → ℝ}
    (hμ : ∀ j, Measurable fun x => μ x j) (ha : ∀ j, Measurable fun x => a x j)
    (hb : ∀ j, Measurable fun x => b x j) :
    Measurable fun x => procMix (μ x) (a x) (b x) :=
  measurable_procSum (fun z => leafM z.1 z.2.1 z.2.2) measurable_leafM n ha hb
    (V := fun x j => 2 * μ x j) (fun j => (hμ j).const_mul 2) measurable_const

/-! ### The pieces of a coordinate (Lemma 22 as a mixture) -/

lemma measurable_piece (μ : ℝ) : Measurable fun p : ℝ × ℝ => piece μ p.1 p.2 := by
  unfold piece
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    (measurable_gPiece μ)

lemma dclass_integrable {B : ℝ} {F : Measure ℝ} {f : ℝ → ℝ} (hD : DClass B F f)
    (hFB : F (Ioi B) = 0) : Integrable id F := by
  have := hD.prob
  refine (integrable_const B).mono' aestronglyMeasurable_id ?_
  filter_upwards [ae_nonneg_of_Iio hD.neg, measure_eq_zero_iff_ae_notMem.mp hFB] with x h0 hB
  simp only [id, Real.norm_eq_abs, abs_of_nonneg h0]
  exact not_lt.mp hB

lemma dclass_Ioi {B : ℝ} {F : Measure ℝ} {f : ℝ → ℝ} (hD : DClass B F f) :
    F (Ioi B) = 0 := by
  obtain ⟨ν, -, -, -, hsupp, -, -, hiff⟩ := slab_lemma_exists hD
  exact (hiff B hD.nonneg).2 (measure_mono_null
    (show Ioi B ⊆ (Icc 0 B)ᶜ from fun x hx h => (mem_Ioi.mp hx).not_ge h.2) hsupp)

lemma dclass_mean_nonneg {B : ℝ} {F : Measure ℝ} {f : ℝ → ℝ} (hD : DClass B F f) :
    0 ≤ ∫ x, x ∂F := integral_nonneg_of_ae (ae_nonneg_of_Iio hD.neg)

/-- **Lemma 22** as a mixture of pieces: `F ∈ 𝒟(B)` with mean `μ` is `∫ piece μ a b pd(da, db)`
for a probability measure `pd` carried by the pieces `(a, b)` for `μ`, with `b ≤ c` for every
`c ≥ 0` with `F((c, ∞)) = 0`. (The atom `π({2μ})` becomes the piece `(2μ, 2μ)`; for `μ = 0`,
`F = δ₀` is the piece `(0, 0)`.) -/
theorem exists_pieces {B : ℝ} {F : Measure ℝ} {f : ℝ → ℝ} (hD : DClass B F f) {c : ℝ}
    (hc : 0 ≤ c) (hFc : F (Ioi c) = 0) :
    ∃ pd : Measure (ℝ × ℝ), IsProbabilityMeasure pd ∧
      (∀ᵐ p ∂pd, IsPiece (∫ x, x ∂F) p.1 p.2 ∧ p.2 ≤ c) ∧
      F = pd.bind fun p => piece (∫ x, x ∂F) p.1 p.2 := by
  have := hD.prob
  set μ := ∫ x, x ∂F with hμdef
  obtain ⟨ν, hν0, hνf, hprob, hsupp, hbind, hmean, hiff⟩ := slab_lemma_exists hD
  have hπ0 := slabMeas_Iio (F := F) hν0
  set π := slabMeas F ν with hπdef
  have hπc : π (Icc 0 c)ᶜ = 0 := by
    have h1 : π (Ioi c) = 0 := (hiff c hc).1 hFc
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hπ0 h1)
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  rcases (dclass_mean_nonneg hD).eq_or_lt with h0 | hpos
  · -- `μ = 0`: `F = δ₀`
    replace h0 : μ = 0 := h0.symm
    refine ⟨Measure.dirac (0, 0), inferInstance, ?_, ?_⟩
    · rw [ae_dirac_eq]
      exact ⟨Or.inr ⟨by simp [h0], by simp [h0]⟩, hc⟩
    · rw [Measure.dirac_bind (measurable_piece μ), h0]
      simp only [piece, ite_true, mul_zero, unifI_self]
      have hz : ∀ᵐ x ∂F, x = 0 := by
        have hi := dclass_integrable hD (dclass_Ioi hD)
        have := (integral_eq_zero_iff_of_nonneg_ae (ae_nonneg_of_Iio hD.neg) hi).1 h0
        exact this
      ext s hs
      rw [Measure.dirac_apply' _ hs]
      by_cases h : (0 : ℝ) ∈ s
      · simp only [h, indicator_of_mem, Pi.one_apply]
        rw [← prob_compl_eq_zero_iff hs]
        exact measure_mono_null (show sᶜ ⊆ {x | ¬x = 0} from fun x hx hx0 => hx (hx0 ▸ h))
          (ae_iff.mp hz)
      · simp only [h, not_false_eq_true, indicator_of_notMem]
        exact measure_mono_null (show s ⊆ {x | ¬x = 0} from fun x hx hx0 => h (hx0 ▸ hx))
          (ae_iff.mp hz)
  · obtain ⟨-, hΔ0, hΔ1⟩ := pairs_lemma_F hD.nonneg hD.neg hD.dens hD.vanish hν0 hνf hpos rfl
    by_cases hΔ : Delta (2 * μ) π = 0
    · have hF := hΔ0 hΔ
      refine ⟨Measure.dirac (2 * μ, 2 * μ), inferInstance, ?_, ?_⟩
      · rw [ae_dirac_eq]
        refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
        have := hFc
        rw [hF] at this
        exact (unifI_Ioi_eq_zero_iff hc (by linarith)).1 this
      · rw [Measure.dirac_bind (measurable_piece μ)]
        simpa [piece] using hF
    · obtain ⟨hF, hmass, hae⟩ := hΔ1 hΔ
      set P := pairMeas (2 * μ) π
      have hP2 : ∀ᵐ p ∂P, p.2 ≤ c := ae_pairMeas_le hπc
      have hle : π {2 * μ} ≤ 1 := prob_le_one
      refine ⟨π {2 * μ} • Measure.dirac (2 * μ, 2 * μ) + P, ⟨?_⟩, ?_, ?_⟩
      · rw [add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one, hmass]
        exact add_tsub_cancel_of_le hle
      · rw [ae_add_measure_iff]
        refine ⟨?_, ?_⟩
        · by_cases h2 : 2 * μ ≤ c
          · refine Measure.ae_smul_measure ?_ _
            rw [ae_dirac_eq]
            exact ⟨Or.inr ⟨rfl, rfl⟩, h2⟩
          · have : π {2 * μ} = 0 :=
              measure_mono_null (show {2 * μ} ⊆ (Icc 0 c)ᶜ from fun x hx h => by
                rw [mem_singleton_iff.mp hx] at h; exact h2 h.2) hπc
            rw [this, zero_smul]
            simp
        · filter_upwards [hae, hP2] with p hp hp2
          exact ⟨Or.inl ⟨hp.1, hp.2.1, hp.2.2.1⟩, hp2⟩
      · ext s hs
        rw [Measure.bind_apply hs (measurable_piece μ).aemeasurable, lintegral_add_measure,
          lintegral_smul_measure, lintegral_dirac]
        conv_lhs => rw [hF]
        rw [add_apply, smul_apply, smul_eq_mul,
          Measure.bind_apply hs (measurable_gPiece μ).aemeasurable]
        congr 1
        · simp only [piece, ite_true]; rfl
        · refine lintegral_congr_ae ?_
          filter_upwards [hae] with p hp
          have : p.1 ≠ p.2 := by linarith [hp.2.1, hp.2.2.1]
          simp [piece, this]

/-! ### The mixture over independent pieces -/

/-- The joint mix of the proof of Theorem 27: the pieces of the coordinates are drawn
independently from `pd j`, and given the pieces the joint mix `procMix` is taken. -/
def pieceMix (μ : Fin n → ℝ) (pd : Fin n → Measure (ℝ × ℝ)) : Measure (Fin n → ℝ) :=
  (Measure.pi pd).bind fun x => procMix μ (fun j => (x j).1) (fun j => (x j).2)

lemma measurable_procMix_pieces (μ : Fin n → ℝ) :
    Measurable fun x : Fin n → ℝ × ℝ => procMix μ (fun j => (x j).1) (fun j => (x j).2) :=
  measurable_procMix (fun _ => measurable_const)
    (fun j => measurable_fst.comp (measurable_pi_apply j))
    (fun j => measurable_snd.comp (measurable_pi_apply j))

/-- The mixture over independent pieces is a joint mix of the mixtures of the pieces, with sum
`∑ μ_j`. -/
theorem pieceMix_spec {μ : Fin n → ℝ} (pd : Fin n → Measure (ℝ × ℝ))
    [hpd : ∀ j, IsProbabilityMeasure (pd j)] (hμ : ∀ j, 0 ≤ μ j) (hs : 0 < ∑ j, μ j)
    (hp : ∀ j, ∀ᵐ p ∂pd j, IsPiece (μ j) p.1 p.2 ∧ p.2 ≤ ∑ j, μ j) :
    IsJointMix (fun j => (pd j).bind fun p => piece (μ j) p.1 p.2) (pieceMix μ pd) ∧
      ∀ᵐ x ∂pieceMix μ pd, ∑ j, x j = ∑ j, μ j := by
  have hK := measurable_procMix_pieces μ
  have hgood : ∀ᵐ x ∂Measure.pi pd, ∀ j, IsPiece (μ j) (x j).1 (x j).2 ∧ (x j).2 ≤ ∑ j, μ j :=
    ae_all_iff.2 fun j => Measure.tendsto_eval_ae_ae.eventually (hp j)
  have hspec : ∀ᵐ x ∂Measure.pi pd,
      IsJointMix (fun j => piece (μ j) (x j).1 (x j).2)
        (procMix μ (fun j => (x j).1) (fun j => (x j).2)) ∧
      ∀ᵐ y ∂procMix μ (fun j => (x j).1) (fun j => (x j).2), ∑ j, y j = ∑ j, μ j := by
    filter_upwards [hgood] with x hx
    exact procMix_spec (fun j => (hx j).1) hμ (fun j => (hx j).2) hs
  have hsumset : MeasurableSet {y : Fin n → ℝ | ¬∑ j, y j = ∑ j, μ j} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  have hsum : ∀ᵐ y ∂pieceMix μ pd, ∑ j, y j = ∑ j, μ j := by
    rw [ae_iff, pieceMix, Measure.bind_apply hsumset hK.aemeasurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hspec] with x hx
    exact ae_iff.mp hx.2
  refine ⟨⟨⟨?_⟩, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  · rw [pieceMix, Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
    rw [lintegral_congr_ae (g := fun _ => 1), lintegral_one, measure_univ]
    filter_upwards [hspec] with x hx
    exact hx.1.1.measure_univ
  · ext t ht
    have hpt : Measurable fun p : ℝ × ℝ => piece (μ j) p.1 p.2 t :=
      (Measure.measurable_coe ht).comp (measurable_piece (μ j))
    rw [Measure.map_apply (measurable_pi_apply j) ht, pieceMix,
      Measure.bind_apply (measurable_pi_apply j ht) hK.aemeasurable,
      Measure.bind_apply ht (measurable_piece (μ j)).aemeasurable,
      ← (measurePreserving_eval pd j).map_eq, lintegral_map hpt (measurable_pi_apply j)]
    refine lintegral_congr_ae ?_
    filter_upwards [hspec] with x hx
    have := congrArg (fun m => m t) (hx.1.2.2 j)
    simp only at this
    rw [Measure.map_apply (measurable_pi_apply j) ht] at this
    exact this

/-! ### Theorem 27 -/

/-- Necessity in Theorem 27 (shown after `(eq:cond)` in the paper): for distributions on
`[0, ∞)` with finite means, the sum of a joint mix is the sum `s` of the means, and every
coordinate is at most `s`; so every `F_j` vanishes on `(s, ∞)`. -/
theorem necessity {F : Fin n → Measure ℝ} (h0 : ∀ j, F j (Iio 0) = 0)
    (hi : ∀ j, Integrable id (F j)) {P : Measure (Fin n → ℝ)} (hP : IsJointMix F P) :
    (∀ᵐ x ∂P, ∑ j, x j = ∑ j, ∫ x, x ∂F j) ∧ ∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0 := by
  obtain ⟨hprob, ⟨c, hc⟩, hmap⟩ := hP
  have hiP : ∀ j, Integrable (fun x : Fin n → ℝ => x j) P := fun j =>
    (integrable_map_measure aestronglyMeasurable_id (measurable_pi_apply j).aemeasurable).1
      (by rw [hmap j]; exact hi j)
  have hint : ∀ j, ∫ x, x j ∂P = ∫ x, x ∂F j := fun j => by
    rw [← hmap j, integral_map (μ := P) (φ := fun x : Fin n → ℝ => x j) (f := fun y : ℝ => y)
      (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id]
  have hcs : c = ∑ j, ∫ x, x ∂F j := by
    have e1 : ∫ x, ∑ j, x j ∂P = c := by
      rw [integral_congr_ae hc, integral_const]; simp
    rw [← e1, integral_finsetSum _ fun j _ => hiP j]
    exact Finset.sum_congr rfl fun j _ => hint j
  have hnn : ∀ j, ∀ᵐ x ∂P, 0 ≤ x j := fun j => by
    have : ∀ᵐ y ∂P.map (fun x => x j), 0 ≤ y := by rw [hmap j]; exact ae_nonneg_of_Iio (h0 j)
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable this
  have hsum : ∀ᵐ x ∂P, ∑ j, x j = ∑ j, ∫ x, x ∂F j := hcs ▸ hc
  refine ⟨hsum, fun j => ?_⟩
  rw [← hmap j, Measure.map_apply (measurable_pi_apply j) measurableSet_Ioi]
  have hall : ∀ᵐ x ∂P, ∀ i, 0 ≤ x i := ae_all_iff.2 hnn
  refine measure_mono_null (fun x hx => ?_) (ae_iff.mp (hsum.and hall))
  intro h
  simp only [mem_preimage, mem_Ioi] at hx
  have : x j ≤ ∑ i, x i :=
    Finset.single_le_sum (fun i _ => h.2 i) (Finset.mem_univ j)
  linarith [h.1]

/-- **Theorem 27** (`j:thm:main`), for `F_j ∈ 𝒟(B_j)` (Definition 19: an atom at `0` and a
non-increasing right-continuous density on `(0, ∞)` vanishing beyond `B_j`) with means
`μ_j`, not all `0`, and `s = ∑ μ_j`: `(F_1, …, F_n)` is jointly mixable iff every `F_j`
vanishes on `(s, ∞)` (that is, the largest right end of the supports is at most `s`). In that
case the joint mix `pieceMix μ pd` of the proof, for the piece distributions `pd` of
Lemma 22, is a joint mix with sum `s`. -/
theorem thm27 {B : Fin n → ℝ} {F : Fin n → Measure ℝ} {f : Fin n → ℝ → ℝ}
    (hD : ∀ j, DClass (B j) (F j) (f j)) (hne : ∃ j, ∫ x, x ∂F j ≠ 0) :
    (JointlyMixable F ↔ ∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0) ∧
    ((∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0) →
      ∃ pd : Fin n → Measure (ℝ × ℝ), (∀ j, IsProbabilityMeasure (pd j)) ∧
        IsJointMix F (pieceMix (fun j => ∫ x, x ∂F j) pd) ∧
        ∀ᵐ x ∂pieceMix (fun j => ∫ x, x ∂F j) pd, ∑ j, x j = ∑ j, ∫ x, x ∂F j) := by
  set μ : Fin n → ℝ := fun j => ∫ x, x ∂F j with hμdef
  have hμ : ∀ j, 0 ≤ μ j := fun j => dclass_mean_nonneg (hD j)
  have hs : 0 < ∑ j, μ j := by
    obtain ⟨j, hj⟩ := hne
    exact lt_of_lt_of_le ((hμ j).lt_of_ne (Ne.symm hj))
      (Finset.single_le_sum (fun i _ => hμ i) (Finset.mem_univ j))
  have suff : (∀ j, F j (Ioi (∑ i, μ i)) = 0) →
      ∃ pd : Fin n → Measure (ℝ × ℝ), (∀ j, IsProbabilityMeasure (pd j)) ∧
        IsJointMix F (pieceMix μ pd) ∧ ∀ᵐ x ∂pieceMix μ pd, ∑ j, x j = ∑ j, μ j := by
    intro hc
    choose pd hpd hae hF using fun j => exists_pieces (hD j) hs.le (hc j)
    obtain ⟨hJ, hsum⟩ := pieceMix_spec pd hμ hs hae
    refine ⟨pd, hpd, ?_, hsum⟩
    convert hJ using 1
    funext j
    exact hF j
  refine ⟨⟨fun ⟨P, hP⟩ => (necessity (fun j => (hD j).neg)
    (fun j => dclass_integrable (hD j) (dclass_Ioi (hD j))) hP).2, fun hc => ?_⟩, suff⟩
  obtain ⟨pd, -, hJ, -⟩ := suff hc
  exact ⟨_, hJ⟩

/-- **Corollary 28** (`j:cor:cm`), for `F ∈ 𝒟(B)` with mean `μ > 0` and `n ≥ 1`: `F` is
`n`-completely mixable iff `F` vanishes on `(nμ, ∞)` (the right end of the support is at most
`nμ`); then the joint mix of Theorem 27 with `F_1 = … = F_n = F` is a complete mix. -/
theorem cor_cm {B : ℝ} {F : Measure ℝ} {f : ℝ → ℝ} (hD : DClass B F f) (hμ : 0 < ∫ x, x ∂F)
    {n : ℕ} (hn : 1 ≤ n) : CompletelyMixable n F ↔ F (Ioi (n * ∫ x, x ∂F)) = 0 := by
  have h := (thm27 (n := n) (B := fun _ => B) (F := fun _ => F) (f := fun _ => f) (fun _ => hD)
    ⟨⟨0, hn⟩, hμ.ne'⟩).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact ⟨fun ⟨P, hP⟩ => h.1 ⟨P, hP⟩ ⟨0, hn⟩, fun hc => h.2 fun _ => hc⟩

/-! ### Concave distribution functions (the class `𝒟(B)`) -/

section ConcaveCdf

variable {G : Measure ℝ} [IsProbabilityMeasure G]

/-- The right derivative of the distribution function of `G`. -/
def rDens (G : Measure ℝ) (x : ℝ) : ℝ :=
  -derivWithin (fun y => -(G (Iic y)).toReal) (Ioi x) x

lemma cdf_mono : Monotone fun x => (G (Iic x)).toReal := fun _ _ h =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 h))

lemma measure_Ioc_cdf {a b : ℝ} (hab : a ≤ b) :
    G (Ioc a b) = ENNReal.ofReal ((G (Iic b)).toReal - (G (Iic a)).toReal) := by
  have e : Iic b \ Iic a = Ioc a b := by
    ext y; simp only [mem_sdiff, mem_Iic, mem_Ioc, not_le]; exact and_comm
  rw [← e, measure_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic.nullMeasurableSet
    (measure_ne_top _ _), ← ENNReal.toReal_sub_of_le (measure_mono (Iic_subset_Iic.2 hab))
    (measure_ne_top _ _), ENNReal.ofReal_toReal]
  exact ENNReal.sub_ne_top (measure_ne_top _ _)

lemma mem_interior_Ici {x : ℝ} (hx : 0 < x) : x ∈ interior (Ici (0 : ℝ)) := by
  rw [interior_Ici]; exact hx

variable (hconc : ConcaveOn ℝ (Ici 0) fun x => (G (Iic x)).toReal)
include hconc

omit [IsProbabilityMeasure G] in
lemma cdf_neg_convex : ConvexOn ℝ (Ici 0) fun x => -(G (Iic x)).toReal := hconc.neg

omit [IsProbabilityMeasure G] in
lemma hasDerivWithinAt_rDens {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (fun x => (G (Iic x)).toReal) (rDens G x) (Ioi x) x := by
  have := ((cdf_neg_convex hconc).hasDerivWithinAt_rightDeriv_of_mem_interior
    (mem_interior_Ici hx)).neg
  have e : (fun x => (G (Iic x)).toReal) = -(fun x => -(G (Iic x)).toReal) := by
    funext y; simp
  rw [e]
  exact this

lemma rDens_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ rDens G x := by
  have h := (cdf_neg_convex hconc).rightDeriv_le_slope_of_mem_interior (mem_interior_Ici hx)
    (show x + 1 ∈ Ici (0 : ℝ) from mem_Ici.2 (by linarith)) (by linarith : x < x + 1)
  have hm := cdf_mono (G := G) (show x ≤ x + 1 by linarith)
  simp only [slope_def_field] at h
  simp only [rDens]
  have : (-(G (Iic (x + 1))).toReal - -(G (Iic x)).toReal) / (x + 1 - x) ≤ 0 := by
    rw [show x + 1 - x = 1 by ring, div_one]; linarith
  linarith

omit [IsProbabilityMeasure G] in
lemma rDens_anti : AntitoneOn (rDens G) (Ioi 0) := by
  intro x hx y hy hxy
  have := (cdf_neg_convex hconc).monotoneOn_rightDeriv (mem_interior_Ici hx)
    (mem_interior_Ici hy) hxy
  simp only [rDens]
  linarith

omit [IsProbabilityMeasure G] in
lemma cdf_continuousOn : ContinuousOn (fun x => (G (Iic x)).toReal) (Ioi 0) := by
  have := hconc.continuousOn_interior
  rwa [interior_Ici] at this

omit [IsProbabilityMeasure G] in
lemma rDens_rc {x : ℝ} (hx : 0 < x) : ContinuousWithinAt (rDens G) (Ici x) x := by
  set H : ℝ → ℝ := fun y => -(G (Iic y)).toReal with hH
  have hc := cdf_neg_convex hconc
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- `rDens` is antitone; the right derivative `-rDens` of `H` is monotone, so `rDens ≤`
    -- `rDens x` near `x`; the lower bound uses the slopes of `H`.
    have hd := (hc.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Ici hx))
    have ht := (hasDerivWithinAt_iff_tendsto_slope' (fun h : x ∈ Ioi x => lt_irrefl x h)).1 hd
    have hlt : derivWithin H (Ioi x) x < -a := by simp only [rDens] at ha; linarith
    obtain ⟨y, hy1, hy2⟩ := ((ht.eventually (gt_mem_nhds hlt)).and
      self_mem_nhdsWithin).exists
    have hy2 : x < y := hy2
    -- the slope `t ↦ slope H t y` is continuous at `x`
    have hcont : ContinuousAt (fun t => slope H t y) x := by
      simp only [slope_def_field]
      refine ContinuousAt.div (continuousAt_const.sub ?_) (continuousAt_const.sub
        continuousAt_id) (sub_ne_zero.2 hy2.ne')
      exact ((cdf_continuousOn hconc).continuousAt (Ioi_mem_nhds hx)).neg
    have hev : ∀ᶠ t in nhds x, slope H t y < -a ∧ t < y :=
      (hcont.eventually (gt_mem_nhds hy1)).and (gt_mem_nhds hy2)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht hxt
    rcases (mem_Ici.mp hxt).lt_or_eq with hxt | rfl
    · have := hc.rightDeriv_le_slope_of_mem_interior (mem_interior_Ici (hx.trans hxt))
        (show y ∈ Ici (0 : ℝ) from mem_Ici.2 (by linarith)) ht.2
      simp only [rDens]
      linarith [ht.1]
    · simp only [rDens]; linarith
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_of_le_of_lt (rDens_anti hconc hx (hx.trans_le ht) ht) ha

omit [IsProbabilityMeasure G] in
lemma integral_rDens {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in a..b, rDens G y = (G (Iic b)).toReal - (G (Iic a)).toReal := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((cdf_continuousOn hconc).mono fun y hy => ha.trans_le hy.1)
    (fun y hy => hasDerivWithinAt_rDens hconc (ha.trans hy.1)) ?_
  refine AntitoneOn.intervalIntegrable ((rDens_anti hconc).mono fun y hy => ?_)
  rw [uIcc_of_le hab] at hy
  exact ha.trans_le hy.1

omit [IsProbabilityMeasure G] in
lemma intervalIntegrable_rDens {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (rDens G) volume a b := by
  refine AntitoneOn.intervalIntegrable ((rDens_anti hconc).mono fun y hy => ?_)
  rw [uIcc_of_le hab] at hy
  exact ha.trans_le hy.1

lemma measure_Ioc_eq_rDens {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    G (Ioc a b) = volume.withDensity (fun x => ENNReal.ofReal (rDens G x)) (Ioc a b) := by
  rw [withDensity_apply _ measurableSet_Ioc, measure_Ioc_cdf hab.le,
    ← integral_rDens hconc ha hab.le, intervalIntegral.integral_of_le hab.le,
    ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_rDens hconc ha hab.le).1]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact rDens_nonneg hconc (ha.trans hy.1)

lemma measure_Ioc_zero_eq_rDens {b : ℝ} (hb : 0 < b) :
    G (Ioc 0 b) = volume.withDensity (fun x => ENNReal.ofReal (rDens G x)) (Ioc 0 b) := by
  set S : ℕ → Set ℝ := fun k => Ioc (b / (k + 2)) b
  have hS : Monotone S := fun k l hkl => Ioc_subset_Ioc_left
    (div_le_div_of_nonneg_left hb.le (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ l + 2)))
  have hU : (⋃ k, S k) = Ioc 0 b := by
    ext y
    simp only [mem_iUnion, mem_Ioc, S]
    constructor
    · rintro ⟨k, h1, h2⟩; exact ⟨lt_of_le_of_lt (by positivity) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨k, hk⟩ := exists_nat_gt (b / y)
      refine ⟨k, ?_, h2⟩
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hk
      nlinarith
  rw [← hU, hS.measure_iUnion, hS.measure_iUnion]
  refine iSup_congr fun k => measure_Ioc_eq_rDens hconc (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- A probability distribution on `[0, ∞)` with a concave distribution function on `[0, ∞)` and
support in `(-∞, B]` lies in `𝒟(B)`, with the right derivative of the distribution function as
the density. -/
theorem dclass_of_concave (h0 : G (Iio 0) = 0) {B : ℝ} (hB : G (Ioi B) = 0) :
    DClass B G (rDens G) where
  nonneg := by
    by_contra hneg
    have : (univ : Set ℝ) ⊆ Iio 0 ∪ Ioi B := fun x _ => by
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_lt_of_le (not_le.mp hneg) h)
    have h1 := measure_mono (μ := G) this
    rw [measure_univ] at h1
    have h2 := (h1.trans (measure_union_le _ _)).trans_eq (by rw [h0, hB, add_zero])
    exact absurd h2 (by simp)
  prob := inferInstance
  neg := h0
  dens := by
    refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
    rw [Measure.restrict_apply measurableSet_Ioc, Slabs.densMeas,
      withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      ← withDensity_apply _ (measurableSet_Ioc.inter measurableSet_Ioi)]
    rcases le_or_gt b 0 with hb | hb
    · have : Ioc a b ∩ Ioi 0 = ∅ := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ioi, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1.2, h.2]
      rw [this, measure_empty, measure_empty]
    rcases le_or_gt a 0 with ha | ha
    · have : Ioc a b ∩ Ioi 0 = Ioc 0 b := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
      rw [this]; exact measure_Ioc_zero_eq_rDens hconc hb
    · have : Ioc a b ∩ Ioi 0 = Ioc a b := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
        constructor
        · rintro ⟨h, -⟩; exact h
        · rintro h; exact ⟨h, by linarith [h.1]⟩
      rw [this]; exact measure_Ioc_eq_rDens hconc ha hab
  anti := rDens_anti hconc
  rc := fun x hx => rDens_rc hconc hx
  vanish := by
    intro x hx
    have hB0 : ∀ y, B ≤ y → (G (Iic y)).toReal = 1 := fun y hy => by
      have : G (Ioi y) = 0 := measure_mono_null (Ioi_subset_Ioi hy) hB
      rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic] at this
      simp [this]
    have hd : HasDerivWithinAt (fun y => -(G (Iic y)).toReal) 0 (Ioi x) x :=
      (hasDerivWithinAt_const x (Ioi x) (-1 : ℝ)).congr
        (fun y hy => by rw [hB0 y (by linarith [mem_Ioi.mp hy])])
        (by rw [hB0 x hx.le])
    simp only [rDens, hd.derivWithin (uniqueDiffWithinAt_Ioi x), neg_zero]

end ConcaveCdf

/-! ### Theorem 27 and Corollary 28 for concave distribution functions -/

/-- **Theorem 27** (`j:thm:main`) as stated in the paper: let `F_1, …, F_n` be distributions on
`[0, ∞)` whose distribution functions are concave on `[0, ∞)`, with finite means `μ_j`, not all
`0`, and `s = ∑ μ_j`. Then `(F_1, …, F_n)` is jointly mixable iff every `F_j` vanishes on
`(s, ∞)`, i.e. the largest right end of the supports is at most `s`. In that case the joint
mix `pieceMix μ pd` of the proof is a joint mix with sum `s`. -/
theorem thm27_concave {F : Fin n → Measure ℝ} [∀ j, IsProbabilityMeasure (F j)]
    (h0 : ∀ j, F j (Iio 0) = 0)
    (hconc : ∀ j, ConcaveOn ℝ (Ici 0) fun x => (F j (Iic x)).toReal)
    (hi : ∀ j, Integrable id (F j)) (hne : ∃ j, ∫ x, x ∂F j ≠ 0) :
    (JointlyMixable F ↔ ∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0) ∧
    ((∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0) →
      ∃ pd : Fin n → Measure (ℝ × ℝ), (∀ j, IsProbabilityMeasure (pd j)) ∧
        IsJointMix F (pieceMix (fun j => ∫ x, x ∂F j) pd) ∧
        ∀ᵐ x ∂pieceMix (fun j => ∫ x, x ∂F j) pd, ∑ j, x j = ∑ j, ∫ x, x ∂F j) := by
  have suff : (∀ j, F j (Ioi (∑ i, ∫ x, x ∂F i)) = 0) →
      ∃ pd : Fin n → Measure (ℝ × ℝ), (∀ j, IsProbabilityMeasure (pd j)) ∧
        IsJointMix F (pieceMix (fun j => ∫ x, x ∂F j) pd) ∧
        ∀ᵐ x ∂pieceMix (fun j => ∫ x, x ∂F j) pd, ∑ j, x j = ∑ j, ∫ x, x ∂F j := fun hc =>
    (thm27 (fun j => dclass_of_concave (hconc j) (h0 j) (hc j)) hne).2 hc
  refine ⟨⟨fun ⟨P, hP⟩ => (necessity h0 hi hP).2, fun hc => ?_⟩, suff⟩
  obtain ⟨pd, -, hJ, -⟩ := suff hc
  exact ⟨_, hJ⟩

/-- **Corollary 28** (`j:cor:cm`): for `n ≥ 1` (the paper has `n ≥ 2`) and a distribution `G` on
`[0, ∞)` with a concave distribution function on `[0, ∞)` and finite mean `μ > 0`, `G` is
`n`-completely mixable iff `G` vanishes on `(nμ, ∞)` (the right end of the support is at most
`nμ`). -/
theorem cor_cm_concave {G : Measure ℝ} [IsProbabilityMeasure G] (h0 : G (Iio 0) = 0)
    (hconc : ConcaveOn ℝ (Ici 0) fun x => (G (Iic x)).toReal) (hi : Integrable id G)
    (hμ : 0 < ∫ x, x ∂G) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n G ↔ G (Ioi (n * ∫ x, x ∂G)) = 0 := by
  have h := (thm27_concave (n := n) (F := fun _ => G) (fun _ => h0) (fun _ => hconc)
    (fun _ => hi) ⟨⟨0, hn⟩, hμ.ne'⟩).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact ⟨fun ⟨P, hP⟩ => h.1 ⟨P, hP⟩ ⟨0, hn⟩, fun hc => h.2 fun _ => hc⟩

/-- **`Homothetic.Cor30 n` holds** for every `n` (Corollary 28, sufficiency). -/
theorem cor30 (n : ℕ) : Homothetic.Cor30 n := by
  intro G hG h0 hconc B hB hμ hBn
  have hD := dclass_of_concave hconc h0 hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0` is impossible: `G` would be `δ₀`, with mean `0`
    exfalso
    have hB0 : B ≤ 0 := by simpa using hBn
    have hz : ∀ᵐ x ∂G, x = 0 := by
      filter_upwards [ae_nonneg_of_Iio h0, measure_eq_zero_iff_ae_notMem.mp hB] with x h1 h2
      exact le_antisymm (by linarith [not_lt.mp (show ¬B < x from h2)]) h1
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) hz] at hμ
    simp at hμ
  · refine (cor_cm hD hμ hn).2 (measure_mono_null (Ioi_subset_Ioi hBn) hB)

/-! ### Borel functions of independent uniform variables -/

lemma map_projIcc_first :
    unifSeq.map (fun ω : ℕ → ℝ => projIcc (0 : ℝ) 1 zero_le_one (ω 0)) =
      (volume : Measure unitInterval) := by
  have h1 : unifSeq.map (fun ω => ω 0) = unifI 0 1 := by
    unfold unifSeq; exact Measure.infinitePi_map_eval _ 0
  have h2 : (volume : Measure unitInterval) =
      (volume.restrict (Icc (0 : ℝ) 1)).map (projIcc 0 1 zero_le_one) := by
    rw [← unitInterval.measurePreserving_subtypeVal.map_eq,
      Measure.map_map continuous_projIcc.measurable measurable_subtypeVal]
    have : (projIcc (0 : ℝ) 1 zero_le_one ∘ Subtype.val : unitInterval → unitInterval) = id := by
      funext x; exact projIcc_val zero_le_one x
    rw [this, Measure.map_id]
  have hu : unifI 0 1 = volume.restrict (Icc (0 : ℝ) 1) := by simp [unifI]
  rw [h2, ← hu, ← h1]
  exact (Measure.map_map continuous_projIcc.measurable (measurable_pi_apply 0)).symm

/-- A measurable family of probability measures on `ℝⁿ` is the law of a Borel function of the
parameter and of a sequence of independent uniform variables. -/
theorem exists_unif_rep {X : Type*} [MeasurableSpace X] (M : X → Measure (Fin n → ℝ))
    (hM : Measurable M) :
    ∃ Ψ : X → (ℕ → ℝ) → (Fin n → ℝ), Measurable (Function.uncurry Ψ) ∧
      ∀ x, IsProbabilityMeasure (M x) → unifSeq.map (Ψ x) = M x := by
  classical
  let M' : X → Measure (Fin n → ℝ) := fun x =>
    if M x univ = 1 then M x else Measure.dirac 0
  have hM' : Measurable M' :=
    Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hM)
      measurable_const) hM measurable_const
  let κ : ProbabilityTheory.Kernel X (Fin n → ℝ) := ⟨M', hM'⟩
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun x => by
    change IsProbabilityMeasure (M' x)
    by_cases h : M x univ = 1
    · simp only [M', h, ↓reduceIte]; exact ⟨h⟩
    · simp only [M', h, ↓reduceIte]; infer_instance⟩
  obtain ⟨f, hf, hfmap⟩ := ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval κ
  have hp : Measurable fun ω : ℕ → ℝ => projIcc (0 : ℝ) 1 zero_le_one (ω 0) :=
    continuous_projIcc.measurable.comp (measurable_pi_apply 0)
  refine ⟨fun x ω => f x (projIcc 0 1 zero_le_one (ω 0)),
    hf.comp (measurable_fst.prodMk (hp.comp measurable_snd)), fun x hx => ?_⟩
  have hfx : Measurable (f x) := hf.comp measurable_prodMk_left
  change unifSeq.map (f x ∘ fun ω => projIcc (0 : ℝ) 1 zero_le_one (ω 0)) = M x
  rw [← Measure.map_map hfx hp, map_projIcc_first, hfmap x]
  change M' x = M x
  simp only [M', hx.measure_univ, ↓reduceIte]

/-! ### Scaled copies of one distribution -/

/-- Scaling a piece. -/
def scaleP (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (t * p.1, t * p.2)

lemma measurable_scaleP (t : ℝ) : Measurable (scaleP t) := by unfold scaleP; fun_prop

lemma isPiece_scale {μ a b t : ℝ} (h : IsPiece μ a b) (ht : 0 ≤ t) :
    IsPiece (t * μ) (t * a) (t * b) := by
  rcases ht.lt_or_eq with ht | rfl
  · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨mul_nonneg ht.le h1, ?_, ?_⟩ <;> nlinarith
    · exact Or.inr ⟨by rw [h1]; ring, by rw [h2]; ring⟩
  · exact Or.inr ⟨by ring, by ring⟩

lemma map_mul_unifI_zero {t ℓ : ℝ} (ht : 0 < t) :
    (unifI 0 ℓ).map (fun x => t * x) = unifI 0 (t * ℓ) := by
  rcases le_or_gt 0 ℓ with hℓ | hℓ
  · rw [map_mul_unifI ht hℓ, mul_zero]
  · have h1 : unifI 0 ℓ = Measure.dirac 0 := by simp [unifI, hℓ.le]
    have h2 : unifI 0 (t * ℓ) = Measure.dirac 0 := by
      simp [unifI, (mul_neg_of_pos_of_neg ht hℓ).le]
    rw [h1, h2, Measure.map_dirac' (measurable_const_mul t), mul_zero]

lemma piece_scale {μ a b t : ℝ} (ht : 0 < t) :
    (piece μ a b).map (fun x => t * x) = piece (t * μ) (t * a) (t * b) := by
  have hm : Measurable fun x : ℝ => t * x := measurable_const_mul t
  by_cases hab : a = b
  · have : t * a = t * b := by rw [hab]
    simp only [piece, hab, ↓reduceIte, this]
    rw [map_mul_unifI_zero ht]; ring_nf
  · have htab : t * a ≠ t * b := fun h' => hab (mul_left_cancel₀ ht.ne' h')
    simp only [piece, hab, htab, ↓reduceIte, gPiece]
    rw [Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul, map_mul_unifI_zero ht,
      map_mul_unifI_zero ht]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have e1 : (t * b - 2 * (t * μ)) / (t * b - t * a) = (b - 2 * μ) / (b - a) := by
      rw [show t * b - 2 * (t * μ) = t * (b - 2 * μ) by ring,
        show t * b - t * a = t * (b - a) by ring, mul_div_mul_left _ _ ht.ne']
    have e2 : (2 * (t * μ) - t * a) / (t * b - t * a) = (2 * μ - a) / (b - a) := by
      rw [show 2 * (t * μ) - t * a = t * (2 * μ - a) by ring,
        show t * b - t * a = t * (b - a) by ring, mul_div_mul_left _ _ ht.ne']
    rw [e1, e2]
    all_goals exact hm.aemeasurable

/-- The pieces of `G.map (t * ·)` are the scaled pieces of `G`. -/
lemma bind_scale {μ : ℝ} {pd : Measure (ℝ × ℝ)} [IsProbabilityMeasure pd]
    (hp : ∀ᵐ p ∂pd, IsPiece μ p.1 p.2) {t : ℝ} (ht : 0 ≤ t) :
    (pd.map (scaleP t)).bind (fun p => piece (t * μ) p.1 p.2) =
      (pd.bind fun p => piece μ p.1 p.2).map (fun x => t * x) := by
  rcases ht.lt_or_eq with ht | rfl
  · ext s hs
    have hm : Measurable fun x : ℝ => t * x := measurable_const_mul t
    rw [Measure.bind_apply hs (measurable_piece _).aemeasurable,
      lintegral_map (f := fun p => piece (t * μ) p.1 p.2 s)
        ((Measure.measurable_coe hs).comp (measurable_piece _)) (measurable_scaleP t),
      Measure.map_apply hm hs,
      Measure.bind_apply (hm hs) (measurable_piece _).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hp] with p hp
    simp only [scaleP]
    rw [← piece_scale ht, Measure.map_apply hm hs]
  · have h1 : pd.map (scaleP 0) = Measure.dirac (0, 0) := by
      have : scaleP 0 = fun _ => ((0 : ℝ), (0 : ℝ)) := by funext p; simp [scaleP]
      rw [this, Measure.map_const, measure_univ, one_smul]
    have : IsProbabilityMeasure (pd.bind fun p => piece μ p.1 p.2) := by
      constructor
      rw [Measure.bind_apply MeasurableSet.univ (measurable_piece _).aemeasurable]
      rw [lintegral_congr_ae (g := fun _ => 1), lintegral_one, measure_univ]
      filter_upwards [hp] with p hp
      rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · have : p.1 ≠ p.2 := by linarith
        simp only [piece, this, ↓reduceIte]
        exact (gPiece_isProb h2 h3).measure_univ
      · simp only [piece, h1, h2, ↓reduceIte]
        exact (unifI_isProb 0 _).measure_univ
    rw [h1, Measure.dirac_bind (measurable_piece _)]
    have : (fun x : ℝ => 0 * x) = fun _ => 0 := by funext x; ring
    rw [this, Measure.map_const, measure_univ, one_smul]
    simp [piece, unifI_self]

/-- The joint mix of scaled copies `G.map (λ_j * ·)`, pulled back to the pieces of `G`. -/
def scaledMix (μ1 : ℝ) (pd : Measure (ℝ × ℝ)) (lam : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun _ : Fin n => pd).bind fun y =>
    procMix (fun j => lam j * μ1) (fun j => lam j * (y j).1) (fun j => lam j * (y j).2)

lemma measurable_scaledMix (μ1 : ℝ) (pd : Measure (ℝ × ℝ)) [IsProbabilityMeasure pd] :
    Measurable (scaledMix (n := n) μ1 pd) := by
  have hK : Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ × ℝ) =>
      procMix (fun j => z.1 j * μ1) (fun j => z.1 j * (z.2 j).1)
        (fun j => z.1 j * (z.2 j).2) :=
    measurable_procMix (fun j => ((measurable_pi_apply j).comp measurable_fst).mul_const _)
      (fun j => ((measurable_pi_apply j).comp measurable_fst).mul
        (measurable_fst.comp ((measurable_pi_apply j).comp measurable_snd)))
      (fun j => ((measurable_pi_apply j).comp measurable_fst).mul
        (measurable_snd.comp ((measurable_pi_apply j).comp measurable_snd)))
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have e : (fun lam => scaledMix (n := n) μ1 pd lam s) = fun lam =>
      ∫⁻ y, procMix (fun j => lam j * μ1) (fun j => lam j * (y j).1)
        (fun j => lam j * (y j).2) s ∂(Measure.pi fun _ : Fin n => pd) := by
    funext lam
    exact Measure.bind_apply hs (hK.comp measurable_prodMk_left).aemeasurable
  rw [e]
  exact ((Measure.measurable_coe hs).comp hK).lintegral_prod_right'

lemma bind_map_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) {g : α → β} (hg : Measurable g) {K : β → Measure γ} (hK : Measurable K) :
    (ν.map g).bind K = ν.bind (K ∘ g) := by
  ext s hs
  rw [Measure.bind_apply hs hK.aemeasurable, Measure.bind_apply hs (hK.comp hg).aemeasurable,
    lintegral_map (f := fun b => K b s) ((Measure.measurable_coe hs).comp hK) hg]
  rfl

lemma scaledMix_eq (μ1 : ℝ) (pd : Measure (ℝ × ℝ)) [IsProbabilityMeasure pd]
    (lam : Fin n → ℝ) :
    scaledMix μ1 pd lam = pieceMix (fun j => lam j * μ1) fun j => pd.map (scaleP (lam j)) := by
  have hpi : (Measure.pi fun _ : Fin n => pd).map (fun y j => scaleP (lam j) (y j)) =
      Measure.pi fun j => pd.map (scaleP (lam j)) := by
    exact Measure.pi_map_pi fun j => (measurable_scaleP _).aemeasurable
  have hsc : Measurable fun (y : Fin n → ℝ × ℝ) (j : Fin n) => scaleP (lam j) (y j) :=
    measurable_pi_iff.mpr fun j => (measurable_scaleP _).comp (measurable_pi_apply j)
  unfold pieceMix scaledMix
  rw [← hpi]
  have hK := measurable_procMix_pieces (n := n) (fun j => lam j * μ1)
  have e : (fun y : Fin n → ℝ × ℝ => procMix (fun j => lam j * μ1) (fun j => lam j * (y j).1)
      (fun j => lam j * (y j).2)) = (fun x : Fin n → ℝ × ℝ => procMix (fun j => lam j * μ1)
        (fun j => (x j).1) (fun j => (x j).2)) ∘ fun y j => scaleP (lam j) (y j) := by
    funext y; simp only [Function.comp, scaleP]
  rw [e]
  exact (bind_map_comp _ hsc hK).symm

lemma measurableSet_piece (μ c : ℝ) :
    MeasurableSet {p : ℝ × ℝ | IsPiece μ p.1 p.2 ∧ p.2 ≤ c} := by
  unfold IsPiece
  exact ((((measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd))).union
    ((measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_eq_fun measurable_snd measurable_const)))).inter
    (measurableSet_le measurable_snd measurable_const)

/-- The joint mix of scaled copies of `G = ∫ piece μ₁ a b pd(da, db)`: for `λ ≥ 0` with
`c λ_j ≤ ∑ λ_i μ₁` (where the pieces have `b ≤ c`) and `∑ λ_i μ₁ > 0`, `scaledMix μ₁ pd λ` is a
joint mix of the `G.map (λ_j * ·)` with sum `∑ λ_i μ₁`. -/
theorem scaledMix_spec {G : Measure ℝ} {pd : Measure (ℝ × ℝ)} [IsProbabilityMeasure pd]
    {μ1 c : ℝ} (hμ1 : 0 ≤ μ1) (hp : ∀ᵐ p ∂pd, IsPiece μ1 p.1 p.2 ∧ p.2 ≤ c)
    (hG : G = pd.bind fun p => piece μ1 p.1 p.2) {lam : Fin n → ℝ} (hlam : ∀ j, 0 ≤ lam j)
    (hs : 0 < ∑ j, lam j * μ1) (hc : ∀ j, c * lam j ≤ ∑ i, lam i * μ1) :
    IsJointMix (fun j => G.map fun x => lam j * x) (scaledMix μ1 pd lam) ∧
      ∀ᵐ x ∂scaledMix μ1 pd lam, ∑ j, x j = ∑ j, lam j * μ1 := by
  rw [scaledMix_eq]
  have hp' : ∀ j, ∀ᵐ p ∂pd.map (scaleP (lam j)),
      IsPiece (lam j * μ1) p.1 p.2 ∧ p.2 ≤ ∑ i, lam i * μ1 := fun j => by
    refine (ae_map_iff (measurable_scaleP _).aemeasurable (measurableSet_piece _ _)).2 ?_
    filter_upwards [hp] with p hp
    refine ⟨isPiece_scale hp.1 (hlam j), ?_⟩
    simp only [scaleP]
    nlinarith [hc j, mul_le_mul_of_nonneg_left hp.2 (hlam j)]
  obtain ⟨hJ, hsum⟩ := pieceMix_spec (fun j => pd.map (scaleP (lam j)))
    (fun j => mul_nonneg (hlam j) hμ1) hs hp'
  refine ⟨?_, hsum⟩
  convert hJ using 1
  funext j
  rw [hG, bind_scale (hp.mono fun p h => h.1) (hlam j)]

/-- **Theorem 27, measurable version, for scaled copies of one distribution**: if
`G ∈ 𝒟(B)` has mean `μ₁` and vanishes on `(c, ∞)`, `c ≥ 0`, then for every `n` there is a Borel
function `Ψ` of `λ ∈ ℝⁿ` and of a sequence of independent uniform variables such that, whenever
`λ ≥ 0`, `∑ λ_i μ₁ > 0` and `c λ_j ≤ ∑ λ_i μ₁` for all `j` (the condition of Theorem 27 for the
`G.map (λ_j * ·)`, whose right ends are at most `c λ_j`), the law of `Ψ λ` is a joint mix of
the `G.map (λ_j * ·)` with sum `∑ λ_i μ₁`. -/
theorem scaled_unif_rep {B : ℝ} {G : Measure ℝ} {g : ℝ → ℝ} (hD : DClass B G g) {c : ℝ}
    (hc : 0 ≤ c) (hGc : G (Ioi c) = 0) (n : ℕ) :
    ∃ Ψ : (Fin n → ℝ) → (ℕ → ℝ) → (Fin n → ℝ), Measurable (Function.uncurry Ψ) ∧
      ∀ lam : Fin n → ℝ, (∀ j, 0 ≤ lam j) → 0 < ∑ j, lam j * ∫ x, x ∂G →
        (∀ j, c * lam j ≤ ∑ i, lam i * ∫ x, x ∂G) →
        IsJointMix (fun j => G.map fun x => lam j * x) (unifSeq.map (Ψ lam)) ∧
          ∀ᵐ x ∂unifSeq.map (Ψ lam), ∑ j, x j = ∑ j, lam j * ∫ x, x ∂G := by
  obtain ⟨pd, hpd, hp, hG⟩ := exists_pieces hD hc hGc
  obtain ⟨Ψ, hΨ, hrep⟩ := exists_unif_rep (scaledMix (n := n) (∫ x, x ∂G) pd)
    (measurable_scaledMix _ pd)
  refine ⟨Ψ, hΨ, fun lam hlam hs hcl => ?_⟩
  have h := scaledMix_spec (dclass_mean_nonneg hD) hp hG hlam hs hcl
  rw [hrep lam h.1.1]
  exact h

/-! ### The laws `H_{k,q,λ}` of frusta (`Thm27Frustum`) -/

section Frustum

open FrustumMix

/-- The density of `H_{k,q,1}` on `(0, ∞)`: `c (1 - x)^m` on `(0, 1 - q)`, `0` beyond. -/
def hDens (m : ℕ) (q : ℝ) (x : ℝ) : ℝ :=
  if x < 1 - q then ((levelPre m q univ)⁻¹).toReal * (1 - x) ^ m else 0

lemma hLaw_dens (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (hLaw m q 1).restrict (Ioi 0) = Slabs.densMeas (hDens m q) := by
  have hφ : Measurable fun s : ℝ => 1 * (1 - s) := by fun_prop
  have hne : (levelPre m q univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (levelPre_univ_ne_zero m hq0 hq1)
  set c := (levelPre m q univ)⁻¹ with hc
  ext S hS
  have hA : MeasurableSet ((fun s : ℝ => 1 * (1 - s)) ⁻¹' (S ∩ Ioi 0)) :=
    hφ (hS.inter measurableSet_Ioi)
  have hL : ∀ T, MeasurableSet T → levelPre m q T =
      ∫⁻ s, (T ∩ Ioc q 1).indicator (fun s => ENNReal.ofReal (s ^ m)) s := fun T hT => by
    rw [levelPre, withDensity_apply _ hT, Measure.restrict_restrict hT,
      lintegral_indicator (hT.inter measurableSet_Ioc)]
  rw [Measure.restrict_apply hS, hLaw, Measure.map_apply hφ (hS.inter measurableSet_Ioi), levelLaw,
    smul_apply, smul_eq_mul, hL _ hA, ← hc, ← lintegral_const_mul _
      ((Measurable.ennreal_ofReal (by fun_prop)).indicator (hA.inter measurableSet_Ioc)),
    Slabs.densMeas, withDensity_apply _ hS, Measure.restrict_restrict hS,
    ← lintegral_indicator (hS.inter measurableSet_Ioi)]
  rw [← (volume.measurePreserving_sub_left (1 : ℝ)).lintegral_comp
    (f := fun s => c * ((fun s : ℝ => 1 * (1 - s)) ⁻¹' (S ∩ Ioi 0) ∩ Ioc q 1).indicator
      (fun s => ENNReal.ofReal (s ^ m)) s)
    ((Measurable.ennreal_ofReal (by fun_prop)).indicator
      (hA.inter measurableSet_Ioc) |>.const_mul c)]
  refine lintegral_congr fun x => ?_
  have e : 1 * (1 - (1 - x)) = x := by ring
  have hmem : (1 - x ∈ (fun s : ℝ => 1 * (1 - s)) ⁻¹' (S ∩ Ioi 0) ∩ Ioc q 1) ↔
      (x ∈ S ∧ 0 < x) ∧ x < 1 - q ∧ 0 ≤ x := by
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ioc, e]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  by_cases hx : x ∈ S ∧ 0 < x
  · have hx' : x ∈ S ∩ Ioi 0 := hx
    by_cases hxq : x < 1 - q
    · have h1 := hmem.2 ⟨hx, hxq, hx.2.le⟩
      rw [indicator_of_mem h1, indicator_of_mem hx']
      simp only [hDens, hxq, ↓reduceIte]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]
    · have h1 : 1 - x ∉ (fun s : ℝ => 1 * (1 - s)) ⁻¹' (S ∩ Ioi 0) ∩ Ioc q 1 :=
        fun h => hxq (hmem.1 h).2.1
      rw [indicator_of_notMem h1, indicator_of_mem hx']
      simp [hDens, hxq]
  · have hx' : x ∉ S ∩ Ioi 0 := hx
    have h1 : 1 - x ∉ (fun s : ℝ => 1 * (1 - s)) ⁻¹' (S ∩ Ioi 0) ∩ Ioc q 1 :=
      fun h => hx (hmem.1 h).1
    rw [indicator_of_notMem h1, indicator_of_notMem hx', mul_zero]

/-- `H_{k,q,1} ∈ 𝒟(1 - q)`. -/
lemma hLaw_dclass (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    DClass (1 - q) (hLaw m q 1) (hDens m q) where
  nonneg := by linarith
  prob := hLaw_isProb m hq0 hq1 1
  neg := by
    refine measure_mono_null (show Iio 0 ⊆ {x | ¬(0 ≤ x ∧ x ≤ (1 - q) * 1)} from
      fun x hx h => (mem_Iio.mp hx).not_ge h.1) ?_
    exact ae_iff.mp (hLaw_ae (m := m) (q := q) zero_le_one)
  dens := hLaw_dens m hq0 hq1
  anti := by
    intro x hx y hy hxy
    simp only [hDens]
    have hK : 0 ≤ ((levelPre m q univ)⁻¹).toReal := ENNReal.toReal_nonneg
    split_ifs with h1 h2 h2
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) m) hK
    · linarith
    · exact mul_nonneg hK (pow_nonneg (by linarith) m)
    · exact le_rfl
  rc := by
    intro x hx
    by_cases hxq : x < 1 - q
    · have : hDens m q =ᶠ[nhds x] fun y => ((levelPre m q univ)⁻¹).toReal * (1 - y) ^ m := by
        filter_upwards [Iio_mem_nhds hxq] with y hy
        simp [hDens, mem_Iio.mp hy]
      exact ((Continuous.continuousAt (by fun_prop)).congr this.symm).continuousWithinAt
    · have : ∀ y ∈ Ici x, hDens m q y = 0 := fun y hy => by
        simp only [hDens, ite_eq_right_iff]
        exact fun h => absurd (lt_of_le_of_lt hy h) hxq
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr this (this x self_mem_Ici)
  vanish := fun x hx => by simp [hDens, not_lt.mpr hx.le]

/-- **`Thm27Frustum m q` holds** for `0 ≤ q < 1`: Theorem 27 for the laws `H_{k,q,λ}`, with the
joint mix a Borel function of `λ` and of independent uniform variables. -/
theorem thm27Frustum (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : Thm27Frustum m q := by
  intro n _
  have hD := hLaw_dclass m hq0 hq1
  have hGc : hLaw m q 1 (Ioi (1 - q)) = 0 := by
    refine measure_mono_null (show Ioi (1 - q) ⊆ {x | ¬(0 ≤ x ∧ x ≤ (1 - q) * 1)} from
      fun x hx h => (mem_Ioi.mp hx).not_ge (by linarith [h.2])) ?_
    exact ae_iff.mp (hLaw_ae (m := m) (q := q) zero_le_one)
  obtain ⟨Ψ, hΨ, hrep⟩ := scaled_unif_rep hD (by linarith : (0 : ℝ) ≤ 1 - q) hGc n
  refine ⟨Ψ, hΨ, fun lam hlam hne hcond => ?_⟩
  have hsum : ∑ j, lam j * ∫ x, x ∂hLaw m q 1 = (1 - muKQ (m + 1) q) * ∑ j, lam j := by
    rw [integral_hLaw hq0 hq1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨i, hi⟩ := hne
  have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hi)
  have hs : 0 < ∑ j, lam j * ∫ x, x ∂hLaw m q 1 := by
    rw [hsum]; nlinarith [hcond i, mul_pos (sub_pos.2 hq1) hpos]
  have hc : ∀ j, (1 - q) * lam j ≤ ∑ i, lam i * ∫ x, x ∂hLaw m q 1 := fun j => by
    rw [hsum]; exact hcond j
  have h := (hrep lam hlam hs hc).1
  convert h using 1
  funext j
  rw [hLaw, hLaw, Measure.map_map (measurable_const_mul _) (by fun_prop)]
  congr 1
  funext s
  simp only [Function.comp, one_mul]

end Frustum

/-! ### The scaled pieces of Theorem 73 (b) (`hT27` of `Scaled.thm73b`) -/

section Scaled73

open Scaled ProbabilityTheory

/-- The single piece of `P_β` for the mean `1`: `(2, 2)` for `β = 2`, `(0, β)` for `β > 2`. -/
def pieceAB (β : ℝ) : ℝ × ℝ := if β = 2 then (2, 2) else (0, β)

lemma measurable_pieceAB : Measurable pieceAB := by
  unfold pieceAB
  exact Measurable.ite (measurableSet_singleton 2) measurable_const
    (measurable_const.prodMk measurable_id)

lemma isPiece_pieceAB {β : ℝ} (hβ : 2 ≤ β) :
    IsPiece 1 (pieceAB β).1 (pieceAB β).2 ∧ (pieceAB β).2 ≤ β := by
  unfold pieceAB
  split_ifs with h
  · exact ⟨Or.inr ⟨by norm_num, by norm_num⟩, by rw [h]⟩
  · exact ⟨Or.inl ⟨le_rfl, by norm_num, by
      simp only; exact lt_of_le_of_ne (by linarith) (Ne.symm (by simpa [eq_comm] using h))⟩,
      le_rfl⟩

lemma pieceP_eq_piece {β : ℝ} (hβ : 2 ≤ β) :
    pieceP β = piece 1 (pieceAB β).1 (pieceAB β).2 := by
  unfold pieceAB pieceP
  split_ifs with h
  · subst h
    simp [piece]
  · have h0 : (0 : ℝ) ≠ β := by intro h'; linarith
    have hb : 0 < β := by linarith
    simp only [piece, h0, ↓reduceIte, gPiece, sub_zero]
    congr 3
    · field_simp
    · ring

lemma scaledPiece_eq_piece {β lam : ℝ} (hβ : 2 ≤ β) (hlam : 0 ≤ lam) :
    scaledPiece β lam = piece (lam * 1) (lam * (pieceAB β).1) (lam * (pieceAB β).2) := by
  rcases hlam.lt_or_eq with h | rfl
  · rw [scaledPiece, pieceP_eq_piece hβ, piece_scale h]
  · have := pieceP_isProb hβ
    simp only [scaledPiece, zero_mul, Measure.map_const, measure_univ, one_smul]
    simp [piece, unifI_self]

/-- **The hypothesis `hT27` of `Scaled.thm73b` holds** for a measurable `β ≥ 2` and `λ ≥ 0`:
there is a Markov kernel `κ` from the level `U` that is, at every `U` with
`β(U) λ_i ≤ ∑ λ_j`, a joint mix of the scaled pieces `λ_i Y`, `Y ∼ P_{β(U)}`, with sum
`∑ λ_j` (Theorem 27 for these pieces, each a single piece of Lemma 22). -/
theorem exists_hT27 {n : ℕ} {β : ℝ → ℝ} (hβm : Measurable β) (hβ2 : ∀ U, 2 ≤ β U)
    {lam : Fin n → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    ∃ κ : Kernel ℝ (Fin n → ℝ), IsMarkovKernel κ ∧
      ∀ U, (∀ i, β U * lam i ≤ ∑ j, lam j) →
        IsJointMix (fun i => scaledPiece (β U) (lam i)) (κ U) ∧
          ∀ᵐ v ∂(κ U), ∑ i, v i = ∑ i, lam i := by
  classical
  rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hlam i).eq_or_lt with h0 | hpos
  · have hz : ∀ i, lam i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hlam i).1 h0.symm i (Finset.mem_univ i)
    refine ⟨Kernel.const ℝ (Measure.dirac 0), inferInstance, fun U _ => ?_⟩
    simp only [Kernel.const_apply]
    have hs : ∀ᵐ v ∂(Measure.dirac (0 : Fin n → ℝ)), ∑ i, v i = ∑ i, lam i := by
      rw [ae_dirac_eq]; simp [hz]
    refine ⟨⟨inferInstance, ⟨_, hs⟩, fun i => ?_⟩, hs⟩
    rw [Measure.map_dirac' (measurable_pi_apply i)]
    show _ = scaledPiece (β U) (lam i)
    rw [hz i, scaledPiece_eq_piece (hβ2 U) le_rfl]
    simp [piece, unifI_self]
  · let M : ℝ → Measure (Fin n → ℝ) := fun U =>
      procMix (fun j => lam j * 1) (fun j => lam j * (pieceAB (β U)).1)
        (fun j => lam j * (pieceAB (β U)).2)
    have hM : Measurable M :=
      measurable_procMix (fun _ => measurable_const)
        (fun j => (measurable_fst.comp (measurable_pieceAB.comp hβm)).const_mul _)
        (fun j => (measurable_snd.comp (measurable_pieceAB.comp hβm)).const_mul _)
    let M' : ℝ → Measure (Fin n → ℝ) := fun U =>
      if M U univ = 1 then M U else Measure.dirac 0
    have hM' : Measurable M' :=
      Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hM)
        measurable_const) hM measurable_const
    let κ : Kernel ℝ (Fin n → ℝ) := ⟨M', hM'⟩
    have hκ : IsMarkovKernel κ := ⟨fun U => by
      change IsProbabilityMeasure (M' U)
      by_cases h : M U univ = 1
      · simp only [M', h, ↓reduceIte]; exact ⟨h⟩
      · simp only [M', h, ↓reduceIte]; infer_instance⟩
    refine ⟨κ, hκ, fun U hU => ?_⟩
    have hspec := procMix_spec (μ := fun j => lam j * 1) (a := fun j => lam j * (pieceAB (β U)).1)
      (b := fun j => lam j * (pieceAB (β U)).2)
      (fun j => isPiece_scale (isPiece_pieceAB (hβ2 U)).1 (hlam j))
      (fun j => by simpa using hlam j)
      (fun j => by
        simp only [mul_one]
        nlinarith [hU j, mul_le_mul_of_nonneg_left (isPiece_pieceAB (hβ2 U)).2 (hlam j)])
      (by simpa using hpos)
    have h1 : M U univ = 1 := hspec.1.1.measure_univ
    have hκU : κ U = M U := by
      change M' U = M U
      simp only [M', h1, ↓reduceIte]
    rw [hκU]
    refine ⟨?_, hspec.2.mono fun x hx => by rw [hx]; simp⟩
    convert hspec.1 using 1
    funext i
    rw [scaledPiece_eq_piece (hβ2 U) (hlam i)]

/-- **Theorem 73 (b)** (`g:thm:scaled`) with the hypothesis from Theorem 27 discharged (for a
measurable `β ≥ 2` and `λ ≥ 0`); the decomposition of Theorem 35 stays a hypothesis. -/
theorem thm73b_of_thm27 {n : ℕ} (F ω : Measure ℝ) [IsProbabilityMeasure ω] (μ : ℝ)
    {l r β : ℝ → ℝ} (hl : Measurable l) (hr : Measurable r) (hβm : Measurable β)
    (hβ2 : ∀ U, 2 ≤ β U)
    (hdecomp : ∀ A, MeasurableSet A →
      F A = ∫⁻ U, (pieceP (β U)).map (pieceMap μ (l U) (r U)) A ∂ω)
    (t lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hβ : ∀ᵐ U ∂ω, ∀ i, β U * lam i ≤ ∑ j, lam j) :
    ∃ κ : Kernel ℝ (Fin n → ℝ), IsMarkovKernel κ ∧
      IsJointMix (fun i => F.map (fun x => t i + lam i * x))
        (ω.bind fun U => (κ U).map (scaledTuple t lam μ (l U) (r U))) ∧
      ∀ᵐ x ∂(ω.bind fun U => (κ U).map (scaledTuple t lam μ (l U) (r U))),
        ∑ i, x i = ∑ i, t i + μ * ∑ i, lam i := by
  obtain ⟨κ, hκ, hT⟩ := exists_hT27 hβm hβ2 hlam
  exact ⟨κ, hκ, thm73b F ω μ hl hr hdecomp t lam κ hT hβ⟩

end Scaled73

/-! ### Consumers of `Thm27Frustum` made unconditional -/

/-- The hypothesis `h27` of `ClassK` (Theorem 61): `Thm27Frustum m q` for all `m` and
`0 ≤ q < 1`. -/
theorem thm27Frustum_all : ∀ (m : ℕ) (q : ℝ), 0 ≤ q → q < 1 → FrustumMix.Thm27Frustum m q :=
  fun m _ hq0 hq1 => thm27Frustum m hq0 hq1

/-- The hypothesis `h27` of `ConeMix` (Theorem 43 (b), Corollaries 44 and 45). -/
theorem thm27Frustum_zero (m : ℕ) : FrustumMix.Thm27Frustum m 0 :=
  thm27Frustum m le_rfl zero_lt_one

section ConeCors

open ConeMix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasureSpace V] [BorelSpace V] [(volume : Measure V).IsAddHaarMeasure] {m : ℕ}

/-- **Corollary 44** (`s:cor:simplex`), unconditionally: for a `k`-simplex `Δ` (`k = m + 1`),
`n ≥ 2`, `t_i ∈ V` and `λ_i ≥ 0` not all zero, `U(t₁ + λ₁Δ), …, U(tₙ + λₙΔ)` are jointly
mixable if and only if `(k + 1) max λ ≤ ∑ λ`. -/
theorem simplex_jointlyMixable_iff' {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) {n : ℕ} (hn : 2 ≤ n) (t : Fin n → V) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0) :
    (JointlyMixable fun i => unifScaled (convexHull ℝ (range p)) (t i) (lam i)) ↔
      ∀ j, ((m : ℝ) + 2) * lam j ≤ ∑ i, lam i :=
  simplex_jointlyMixable_iff thm27Frustum_zero hp hV hn t lam hlam hne

/-- **Corollary 44**, last sentence, unconditionally: for `n ≥ 1` the uniform distribution on
a `d`-simplex (`d = m + 1`) is `n`-completely mixable if and only if `n ≥ d + 1`. -/
theorem simplex_completelyMixable_iff' {p : Fin (m + 2) → V} (hp : AffineIndependent ℝ p)
    (hV : Module.finrank ℝ V = m + 1) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (convexHull ℝ (range p))) ↔ m + 2 ≤ n :=
  simplex_completelyMixable_iff thm27Frustum_zero hp hV hn

/-- **Corollary 45**, last sentence, unconditionally: for `n ≥ 1` the uniform distribution on a
pyramid over a parallelotope in dimension `d = m' + 2` is `n`-completely mixable if and only if
`n ≥ d + 1`. -/
theorem pyramid_completelyMixable_iff' {m' : ℕ} {o a : V} {u : Fin (m' + 1) → V}
    (hu : LinearIndependent ℝ u) (ha : a ∉ affineSpan ℝ (parallelotope o u))
    (hV : Module.finrank ℝ V = m' + 2) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (convexHull ℝ (insert a (parallelotope o u)))) ↔ m' + 3 ≤ n :=
  pyramid_completelyMixable_iff (thm27Frustum_zero _) hu ha hV hn

end ConeCors

end Theorem27

end Mixes
