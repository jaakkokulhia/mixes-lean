import Mixes.AsymThree
import Mixes.AsymWindow

set_option linter.deprecated false

/-!
# Borel dependence of the complete mixes of densities with two steps

Discharges the hypothesis `Mixes.AsymThree.H_twoStepBorel`: for `m ≥ 3` there is a Markov
kernel `(a, b) ↦` an `m`-complete mix of the density `g_{a,b}` (`TwoStep.g`) with sum `m`, for
`0 < a < 2 < b ≤ m`.

## Construction

* The mixture of admissible tuples is the explicit one of Theorem `m:thm:two` in `TwoStep.lean`
  (`mixI` if `a ≤ 1`, `mixII` otherwise; `Mx`). Its weights and the endpoints of its intervals
  are Borel functions of `(a, b)` (`measurable_W`, `measurable_ivMx`): the case distinctions are
  Borel sets, `betaStar` is a Borel `ℕ`-valued function, and for fixed multiplicities the
  endpoints are continuous.
* Lemma 1 is applied with the measurable choice of `AsymWindow` (the first good partition in a
  fixed list), here for a parameter in any measurable space (`jmK`, `mixK`); Lemma 3 is
  `lem_sym`.
* `KT m` is that mixture inside the parameter range and the point mass at `0` outside.

## Main results

* `KT_spec`, `twoStepBorel : AsymThree.H_twoStepBorel`.
* `prop_three_tb` (Proposition `as:prop:three`), `rem_three_tb` (Remark `as:rem:three`),
  `three_core_tb`, `three_scaled_tb`, and `cor_three_tb`, `cor_three_mixable_tb`,
  `cor_three_a_tb`, `cor_three_b_tb`, `cor_three_c_tb` (Corollary `as:cor:three`, still under the
  hypothesis `H_conc_a`): the results of `AsymThree` without `H_twoStepBorel`.

## Differences from the paper

* Tuples of weight `0` are replaced by the admissible tuple `m · [0, 2]` (they do not contribute).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Mixes.TwoStepBorel

open Classical
open AsymWindow

/-! ### Lemma 1 with measurable choices, for a parameter in any measurable space -/

section Param

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-- The joint mix of Lemma 1 for a tuple depending on a parameter `p`, as a function of
`(p, ξ)`: the first good candidate partition in a fixed list. -/
def jmVec (l r : α → Fin n → ℝ) (q : α × V2) : Fin n → ℝ :=
  firstVec (l q.1) (r q.1) (Finset.univ : Finset (Cand n)).toList q.2

/-- The law of `jmVec` for a fixed parameter. -/
def jmK (l r : α → Fin n → ℝ) (p : α) : Measure (Fin n → ℝ) :=
  archPlane.map fun ξ => jmVec l r (p, ξ)

lemma measurable_candVec {l r : α → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (c : Cand n) : Measurable fun q : α × V2 => candVec (l q.1) (r q.1) c q.2 := by
  have hl' : ∀ j, Measurable fun q : α × V2 => l q.1 j :=
    fun j => (measurable_pi_apply j).comp (hl.comp measurable_fst)
  have hr' : ∀ j, Measurable fun q : α × V2 => r q.1 j :=
    fun j => (measurable_pi_apply j).comp (hr.comp measurable_fst)
  have ha : Measurable fun q : α × V2 => r q.1 c.1 - l q.1 c.1 := (hr' _).sub (hl' _)
  have hS : ∀ G : Finset (Fin n), Measurable fun q : α × V2 => ∑ j ∈ G, (r q.1 j - l q.1 j) :=
    fun G => Finset.measurable_sum _ fun j _ => (hr' j).sub (hl' j)
  have hx := measurable_triX ha (hS c.2.1) (hS c.2.2)
  have hy := measurable_triY ha (hS c.2.1) (hS c.2.2)
  have hEk : Measurable fun q : α × V2 => triEk (r q.1 c.1 - l q.1 c.1) := by
    unfold triEk; exact ha.smul_const _
  have hEG : Measurable fun q : α × V2 => triEG (r q.1 c.1 - l q.1 c.1)
      (∑ j ∈ c.2.1, (r q.1 j - l q.1 j)) (∑ j ∈ c.2.2, (r q.1 j - l q.1 j)) := by
    unfold triEG; exact ((hx.sub ha).smul_const _).add (hy.smul_const _)
  have hEH : Measurable fun q : α × V2 => triEH (r q.1 c.1 - l q.1 c.1)
      (∑ j ∈ c.2.1, (r q.1 j - l q.1 j)) (∑ j ∈ c.2.2, (r q.1 j - l q.1 j)) := by
    unfold triEH; exact ((hx.smul_const _).add (hy.smul_const _)).neg
  rw [measurable_pi_iff]
  intro j
  simp only [candVec, archVec]
  split_ifs
  · exact ((hl' j).add (hr' j)).div_const _ |>.add (measurable_const.mul (hEk.inner measurable_snd))
  · exact ((hl' j).add (hr' j)).div_const _ |>.add
      ((((hr' j).sub (hl' j)).div (measurable_const.mul (hS _))).mul (hEG.inner measurable_snd))
  · exact ((hl' j).add (hr' j)).div_const _ |>.add
      ((((hr' j).sub (hl' j)).div (measurable_const.mul (hS _))).mul (hEH.inner measurable_snd))

lemma measurableSet_candOK {l r : α → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (c : Cand n) : MeasurableSet {p | CandOK (l p) (r p) c} := by
  have hl' : ∀ j, Measurable fun p => l p j := fun j => (measurable_pi_apply j).comp hl
  have hr' : ∀ j, Measurable fun p => r p j := fun j => (measurable_pi_apply j).comp hr
  have ha : Measurable fun p => r p c.1 - l p c.1 := (hr' _).sub (hl' _)
  have hS : ∀ G : Finset (Fin n), Measurable fun p => ∑ j ∈ G, (r p j - l p j) :=
    fun G => Finset.measurable_sum _ fun j _ => (hr' j).sub (hl' j)
  simp only [CandOK, Set.ofPred_and, Set.ofPred_or]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  refine MeasurableSet.union ?_ ?_
  · exact (measurableSet_lt measurable_const ha).inter
      ((measurableSet_le ((hS _).sub (hS _)).abs ha).inter
        (measurableSet_le ha ((hS _).add (hS _))))
  · exact (measurableSet_eq_fun ha measurable_const).inter
      ((measurableSet_eq_fun (hS _) measurable_const).inter
        (measurableSet_eq_fun (hS _) measurable_const))

lemma measurable_firstVec {l r : α → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (L : List (Cand n)) : Measurable fun q : α × V2 => firstVec (l q.1) (r q.1) L q.2 := by
  induction L with
  | nil => exact measurable_const
  | cons c L ih =>
    simp only [firstVec, List.foldr_cons]
    exact Measurable.ite (measurable_fst (measurableSet_candOK hl hr c))
      (measurable_candVec hl hr c) ih

lemma measurable_jmVec {l r : α → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r) :
    Measurable (jmVec l r) := measurable_firstVec hl hr _

lemma measurable_jmK_apply {l r : α → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) : Measurable fun p => jmK l r p s := by
  have hm := measurable_jmVec hl hr
  have : (fun p => jmK l r p s) = fun p => archPlane (Prod.mk p ⁻¹' (jmVec l r ⁻¹' s)) := by
    funext p
    have hm' : Measurable fun ξ : V2 => jmVec l r (p, ξ) := hm.comp measurable_prodMk_left
    rw [jmK, Measure.map_apply hm' hs]; rfl
  rw [this]
  exact measurable_measure_prodMk_left (hm hs)

omit [MeasurableSpace α] in
lemma jmK_spec {l r : α → Fin n → ℝ} (hn : 0 < n) {p : α} (hle : ∀ j, l p j ≤ r p j)
    (hpoly : ∀ j, 2 * (r p j - l p j) ≤ ∑ i, (r p i - l p i)) :
    IsJointMix (fun j => unifI (l p j) (r p j)) (jmK l r p) ∧
      ∀ᵐ x ∂(jmK l r p), ∑ j, x j = 1 / 2 * ∑ j, (l p j + r p j) := by
  obtain ⟨c, hc⟩ := exists_candOK hn hle hpoly
  obtain ⟨d, hd, hdv⟩ := firstVec_spec (l p) (r p) (Finset.univ : Finset (Cand n)).toList
    ⟨c, Finset.mem_toList.2 (Finset.mem_univ c), hc⟩
  have : jmK l r p = archPlane.map (candVec (l p) (r p) d) := by
    rw [jmK]; congr 1; funext ξ; exact hdv ξ
  rw [this]
  exact candVec_jointMix hle hd

/-- Choose the tuple `i` with probability `w i p`, draw the joint mix of Lemma 1 for it and
permute the coordinates uniformly at random (Lemma 3). -/
def mixK {ι : Type*} [Fintype ι] (w : ι → α → ℝ) (l r : ι → α → Fin n → ℝ) (p : α) :
    Measure (Fin n → ℝ) :=
  mixture (fun i => ENNReal.ofReal (w i p)) fun i => permAvg (jmK (l i) (r i) p)

lemma measurable_mixK {ι : Type*} [Fintype ι] {w : ι → α → ℝ} {l r : ι → α → Fin n → ℝ}
    (hw : ∀ i, Measurable (w i)) (hl : ∀ i, Measurable (l i)) (hr : ∀ i, Measurable (r i)) :
    Measurable (mixK w l r) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [mixK, mixture, permAvg, sum_apply, smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => (hw i).ennreal_ofReal.mul
    (measurable_const.mul (Finset.measurable_sum _ fun π _ => ?_))
  have : (fun p => (jmK (l i) (r i) p).map (fun x => x ∘ π) s) =
      fun p => jmK (l i) (r i) p ((fun x => x ∘ π) ⁻¹' s) := by
    funext p; rw [Measure.map_apply (measurable_comp_perm π) hs]
  rw [this]
  exact measurable_jmK_apply (hl i) (hr i) (measurable_comp_perm π hs)

omit [MeasurableSpace α] in
lemma mixK_spec {ι : Type*} [Fintype ι] {w : ι → α → ℝ} {l r : ι → α → Fin n → ℝ}
    (hn : 0 < n) {p : α} (hw0 : ∀ i, 0 ≤ w i p) (hw1 : ∑ i, w i p = 1)
    (hle : ∀ i j, l i p j ≤ r i p j)
    (hpoly : ∀ i j, 2 * (r i p j - l i p j) ≤ ∑ j', (r i p j' - l i p j')) (s : ℝ)
    (hs : ∀ i, ∑ j, (l i p j + r i p j) = 2 * s) :
    IsCompleteMix n (∑ i, ENNReal.ofReal (w i p) •
        ((n : ℝ≥0∞)⁻¹ • ∑ j, unifI (l i p j) (r i p j))) (mixK w l r p) ∧
      ∀ᵐ x ∂(mixK w l r p), ∑ j, x j = s := by
  have hw : ∑ i, ENNReal.ofReal (w i p) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
  refine lem_sym _ hw (fun i j => unifI (l i p j) (r i p j)) _ s
    (fun i => (jmK_spec hn (hle i) (hpoly i)).1) fun i => ?_
  filter_upwards [(jmK_spec hn (hle i) (hpoly i)).2] with x hx
  rw [hx, hs i]; ring

/-- A function of a natural-number valued measurable function and the parameter. -/
lemma measurable_natComp {β : Type*} [MeasurableSpace β] {F : ℕ → α → β}
    (hF : ∀ k, Measurable (F k)) {k : α → ℕ} (hk : Measurable k) :
    Measurable fun p => F (k p) p :=
  (measurable_from_prod_countable_left (f := fun q : α × ℕ => F q.2 q.1) hF).comp
    (measurable_id.prodMk hk)

end Param

/-! ### Block tuples as vectors -/

open TwoStep

/-- The `j`-th interval of a block tuple (`(0, 0)` beyond its size). -/
def iv (t : Tup) (j : ℕ) : ℝ × ℝ := t.expand.getD j (0, 0)

lemma iv_eq_getElem {n : ℕ} (t : Tup) (h : t.size = n) (j : Fin n) :
    iv t j = t.expand[(j : ℕ)]'(by rw [Tup.length_expand, h]; exact j.2) := by
  unfold iv; rw [List.getD_eq_getElem]

lemma sum_fin_iv {M : Type*} [AddCommMonoid M] {n : ℕ} (t : Tup) (h : t.size = n)
    (f : ℝ × ℝ → M) : ∑ j : Fin n, f (iv t j) = (t.map fun B => B.c • f (B.l, B.r)).sum := by
  have hl : t.expand.length = n := by rw [Tup.length_expand, h]
  rw [← Tup.sum_expand, ← Tup.sum_fin_expand t hl]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iv_eq_getElem t h]; rfl

lemma iv_mem {n : ℕ} (t : Tup) (h : t.size = n) (j : Fin n) :
    ∃ B ∈ t, 0 < B.c ∧ iv t j = (B.l, B.r) := by
  rw [iv_eq_getElem t h]; exact Tup.mem_expand.mp (List.getElem_mem _)

lemma adm_le {n : ℕ} {t : Tup} (h : t.Adm n) (j : Fin n) : (iv t j).1 ≤ (iv t j).2 := by
  obtain ⟨B, hB, -, he⟩ := iv_mem t h.size j
  rw [he]; exact h.le B hB

lemma adm_lenSum {n : ℕ} {t : Tup} (h : t.Adm n) :
    ∑ j : Fin n, ((iv t j).2 - (iv t j).1) = t.lenSum := by
  rw [sum_fin_iv t h.size (fun q => q.2 - q.1), Tup.lenSum]
  congr 1; apply List.map_congr_left; intro B _; rw [nsmul_eq_mul]

lemma adm_poly {n : ℕ} {t : Tup} (h : t.Adm n) (j : Fin n) :
    2 * ((iv t j).2 - (iv t j).1) ≤ ∑ i : Fin n, ((iv t i).2 - (iv t i).1) := by
  rw [adm_lenSum h]
  obtain ⟨B, hB, hc, he⟩ := iv_mem t h.size j
  rw [he]; exact h.polygon B hB hc

lemma adm_mid {n : ℕ} {t : Tup} (h : t.Adm n) :
    ∑ j : Fin n, ((iv t j).1 + (iv t j).2) = 2 * n := by
  rw [sum_fin_iv t h.size (fun q => q.1 + q.2), ← h.mid, Tup.midSum]
  congr 1; apply List.map_congr_left; intro B _; rw [nsmul_eq_mul]

lemma sum_unifI_iv {n : ℕ} {t : Tup} (h : t.size = n) :
    ∑ j : Fin n, unifI (iv t j).1 (iv t j).2 = t.measure :=
  sum_fin_iv t h (fun q => unifI q.1 q.2)

/-- Tuples of blocks with fixed multiplicities and endpoints depending on a parameter. -/
abbrev PTup (α : Type*) := List (ℕ × (α → ℝ) × (α → ℝ))

/-- The block tuple at the parameter `p`. -/
def PTup.inst {α : Type*} (P : PTup α) (p : α) : Tup := P.map fun q => ⟨q.1, q.2.1 p, q.2.2 p⟩

lemma measurable_iv_inst {α : Type*} [MeasurableSpace α] (P : PTup α)
    (hP : ∀ q ∈ P, Measurable q.2.1 ∧ Measurable q.2.2) (j : ℕ) :
    Measurable fun p => iv (PTup.inst P p) j := by
  induction P generalizing j with
  | nil => simp only [iv, PTup.inst, List.map_nil, Tup.expand, List.flatMap_nil, List.getD_nil];
           exact measurable_const
  | cons q P ih =>
    have hq := hP q List.mem_cons_self
    have ih' := ih (fun q' h => hP q' (List.mem_cons_of_mem _ h))
    have e : ∀ p, (PTup.inst (q :: P) p).expand =
        List.replicate q.1 (q.2.1 p, q.2.2 p) ++ (PTup.inst P p).expand := fun p => by
      simp [PTup.inst, Tup.expand]
    by_cases hj : j < q.1
    · have : (fun p => iv (PTup.inst (q :: P) p) j) = fun p => (q.2.1 p, q.2.2 p) := by
        funext p
        rw [iv, e, List.getD_append _ _ _ _ (by simpa using hj), List.getD_replicate (h := hj)]
      rw [this]; exact hq.1.prodMk hq.2
    · have : (fun p => iv (PTup.inst (q :: P) p) j) = fun p => iv (PTup.inst P p) (j - q.1) := by
        funext p
        rw [iv, e, List.getD_append_right _ _ _ _ (by simp; omega), List.length_replicate]; rfl
      rw [this]; exact ih' _

/-! ### The mixtures of Theorem `m:thm:two` as measurable functions of `(a, b)` -/

/-- The weight of the `i`-th tuple of a mixture (`0` beyond its length). -/
def wOf (M : Mix) (i : ℕ) : ℝ := (M.getD i (0, [])).1

/-- The `i`-th tuple of a mixture (empty beyond its length). -/
def tOf (M : Mix) (i : ℕ) : Tup := (M.getD i (0, [])).2

section MeasMix

variable {α : Type*} [MeasurableSpace α] {A B : α → ℝ} (hA : Measurable A) (hB : Measurable B)
include hA hB

lemma measurable_u (n β : ℕ) : Measurable fun p => u n (A p) (B p) β := by
  unfold u; fun_prop

lemma measurable_findGreatest (n : ℕ) (k : ℕ) :
    Measurable fun p => Nat.findGreatest (fun β => 0 ≤ u n (A p) (B p) β) k := by
  induction k with
  | zero => simp only [Nat.findGreatest_zero]; exact measurable_const
  | succ k ih =>
    simp only [Nat.findGreatest_succ]
    exact Measurable.ite (measurableSet_le measurable_const (measurable_u hA hB n (k + 1)))
      measurable_const ih

lemma measurable_betaStar (n : ℕ) : Measurable fun p => betaStar n (A p) (B p) :=
  measurable_findGreatest hA hB n (n - 1)

lemma measurable_iv_S (n β i j : ℕ) : Measurable fun p => iv (tOf (S n (A p) (B p) β) i) j := by
  rcases i with _ | _ | i
  · exact measurable_iv_inst [(n - 1 - β, fun _ => 0, A), (β - 1, fun _ => 0, B), (1, A, B),
      (1, fun _ => 0, fun p => u n (A p) (B p) β)] (by simp [hA, hB, measurable_u hA hB]) j
  · exact measurable_iv_inst [(n - β, fun _ => 0, A), (β - 1, fun _ => 0, B),
      (1, fun p => u n (A p) (B p) β, B)] (by simp [hA, hB, measurable_u hA hB]) j
  · simp only [tOf, S, List.getD_cons_succ, List.getD_nil, iv, Tup.expand, List.flatMap_nil]
    exact measurable_const

lemma measurable_w_S (n β i : ℕ) : Measurable fun p => wOf (S n (A p) (B p) β) i := by
  rcases i with _ | _ | i
  · simp only [wOf, S, List.getD_cons_zero]; exact (measurable_u hA hB n β).div hB
  · simp only [wOf, S, List.getD_cons_succ, List.getD_cons_zero]
    exact measurable_const.sub ((measurable_u hA hB n β).div hB)
  · simp only [wOf, S, List.getD_cons_succ, List.getD_nil]; exact measurable_const

lemma measurable_iv_SD (n i j : ℕ) : Measurable fun p => iv (tOf (SD n (A p) (B p)) i) j := by
  rcases i with _ | _ | i
  · exact measurable_iv_inst [(n - 2, fun _ => 0, A), (2, fun p => u n (A p) (B p) 2 / 2, B)]
      (by simp [hA, hB, (measurable_u hA hB n 2).div_const]) j
  · exact measurable_iv_inst [(n - 3, fun _ => 0, A), (1, fun _ => 0, fun p => u n (A p) (B p) 2 / 2),
      (1, A, B), (1, fun p => u n (A p) (B p) 2 / 2, B)]
      (by simp [hA, hB, (measurable_u hA hB n 2).div_const]) j
  · simp only [tOf, SD, List.getD_cons_succ, List.getD_nil, iv, Tup.expand, List.flatMap_nil]
    exact measurable_const

lemma measurable_w_SD (n i : ℕ) : Measurable fun p => wOf (SD n (A p) (B p)) i := by
  rcases i with _ | _ | i
  · simp only [wOf, SD, List.getD_cons_zero]
    exact measurable_const.sub ((measurable_u hA hB n 2).div hB)
  · simp only [wOf, SD, List.getD_cons_succ, List.getD_cons_zero]
    exact (measurable_u hA hB n 2).div hB
  · simp only [wOf, SD, List.getD_cons_succ, List.getD_nil]; exact measurable_const

lemma measurableSet_caseA (n : ℕ) : MeasurableSet {p | u n (A p) (B p) 1 ≤ B p} :=
  measurableSet_le (measurable_u hA hB n 1) hB

lemma measurableSet_caseB (n : ℕ) : MeasurableSet {p | 4 ≤ n ∧ 0 ≤ u n (A p) (B p) 3} :=
  (MeasurableSet.const _).inter (measurableSet_le measurable_const (measurable_u hA hB n 3))

lemma measurableSet_caseC (n : ℕ) : MeasurableSet {p | u n (A p) (B p) 2 ≤ ((n : ℝ) - 2) * A p} :=
  measurableSet_le (measurable_u hA hB n 2) (measurable_const.mul hA)

lemma measurable_iv_mixI (n i j : ℕ) : Measurable fun p => iv (tOf (mixI n (A p) (B p)) i) j := by
  unfold mixI
  simp only [apply_ite (fun M => iv (tOf M i) j)]
  exact Measurable.ite (measurableSet_caseA hA hB n) (measurable_iv_S hA hB n 1 i j)
    (Measurable.ite (measurableSet_caseB hA hB n)
      (measurable_natComp (F := fun k p => iv (tOf (S n (A p) (B p) k) i) j)
        (fun k => measurable_iv_S hA hB n k i j) (measurable_betaStar hA hB n))
      (Measurable.ite (measurableSet_caseC hA hB n) (measurable_iv_S hA hB n 2 i j)
        (measurable_iv_SD hA hB n i j)))

lemma measurable_w_mixI (n i : ℕ) : Measurable fun p => wOf (mixI n (A p) (B p)) i := by
  unfold mixI
  simp only [apply_ite (fun M => wOf M i)]
  exact Measurable.ite (measurableSet_caseA hA hB n) (measurable_w_S hA hB n 1 i)
    (Measurable.ite (measurableSet_caseB hA hB n)
      (measurable_natComp (F := fun k p => wOf (S n (A p) (B p) k) i)
        (fun k => measurable_w_S hA hB n k i) (measurable_betaStar hA hB n))
      (Measurable.ite (measurableSet_caseC hA hB n) (measurable_w_S hA hB n 2 i)
        (measurable_w_SD hA hB n i)))

end MeasMix

lemma getD_map_scale (L : Mix) (c : ℝ) (i : ℕ) :
    (L.map fun q => (c * q.1, q.2)).getD i (0, []) =
      (c * (L.getD i (0, [])).1, (L.getD i (0, [])).2) := by
  induction L generalizing i with
  | nil => simp
  | cons q L ih => cases i <;> simp only [List.map_cons, List.getD_cons_zero, List.getD_cons_succ, ih]

lemma measurable_iv_mixII (n i j : ℕ) :
    Measurable fun p : ℝ × ℝ => iv (tOf (mixII n p.1 p.2) i) j := by
  rcases i with _ | i
  · exact measurable_iv_inst [(n, fun p : ℝ × ℝ => 2 - p.1, fun p => p.1)]
      (by simp; constructor <;> fun_prop) j
  · simp only [tOf, mixII, List.getD_cons_succ, getD_map_scale]
    exact measurable_iv_mixI (A := fun p : ℝ × ℝ => 2 - p.1) (B := Prod.snd) (by fun_prop)
      measurable_snd n i j

lemma measurable_w_mixII (n i : ℕ) : Measurable fun p : ℝ × ℝ => wOf (mixII n p.1 p.2) i := by
  rcases i with _ | i
  · simp only [wOf, mixII, List.getD_cons_zero, theta]; fun_prop
  · simp only [wOf, mixII, List.getD_cons_succ, getD_map_scale]
    refine (measurable_const.sub (by unfold theta; fun_prop : Measurable fun p : ℝ × ℝ => theta p.1 p.2)).mul ?_
    exact measurable_w_mixI (A := fun p : ℝ × ℝ => 2 - p.1) (B := Prod.snd) (by fun_prop)
      measurable_snd n i

/-! ### Good mixtures read by index -/

lemma sum_fin_getD {β M : Type*} [AddCommMonoid M] (L : List β) (d : β) (f : β → M)
    (hd : f d = 0) : ∀ k, L.length ≤ k → ∑ i : Fin k, f (L.getD i d) = (L.map f).sum := by
  induction L with
  | nil => intro k _; simp [hd]
  | cons x L ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
      List.map_cons, List.sum_cons]
    rw [ih k (by simp at hk; omega)]

lemma mem_or_default (M : Mix) (i : ℕ) : M.getD i (0, []) ∈ M ∨ M.getD i (0, []) = (0, []) := by
  by_cases h : i < M.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
  · right; exact List.getD_eq_default _ _ (not_lt.1 h)

lemma wOf_nonneg {n : ℕ} {b : ℝ} {M : Mix} (hG : M.Good n b) (i : ℕ) : 0 ≤ wOf M i := by
  rcases mem_or_default M i with h | h
  · exact hG.nonneg _ h
  · rw [wOf, h]

lemma adm_of_pos {n : ℕ} {b : ℝ} {M : Mix} (hG : M.Good n b) {i : ℕ} (hi : 0 < wOf M i) :
    (tOf M i).Adm n ∧ (tOf M i).Inside b := by
  rcases mem_or_default M i with h | h
  · exact hG.adm _ h hi
  · rw [wOf, h] at hi; exact absurd hi (lt_irrefl 0)

/-! ### The kernel -/

/-- The mixture of Theorem `m:thm:two` for `g_{a,b}`: part (i) if `a ≤ 1`, part (ii) otherwise. -/
def Mx (m : ℕ) (p : ℝ × ℝ) : Mix := if p.1 ≤ 1 then mixI m p.1 p.2 else mixII m p.1 p.2

/-- The weight of the `i`-th tuple. -/
def W (m : ℕ) (i : Fin 3) (p : ℝ × ℝ) : ℝ := wOf (Mx m p) i

/-- The left ends of the `i`-th tuple (replaced by `0` if its weight is not positive). -/
def Lv (m : ℕ) (i : Fin 3) (p : ℝ × ℝ) : Fin m → ℝ :=
  fun j => if 0 < W m i p then (iv (tOf (Mx m p) i) j).1 else 0

/-- The right ends of the `i`-th tuple (replaced by `2` if its weight is not positive). -/
def Rv (m : ℕ) (i : Fin 3) (p : ℝ × ℝ) : Fin m → ℝ :=
  fun j => if 0 < W m i p then (iv (tOf (Mx m p) i) j).2 else 2

lemma measurable_W (m : ℕ) (i : Fin 3) : Measurable (W m i) := by
  unfold W Mx
  simp only [apply_ite (fun M => wOf M i)]
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (measurable_w_mixI measurable_fst measurable_snd m i) (measurable_w_mixII m i)

lemma measurable_ivMx (m : ℕ) (i : Fin 3) (j : ℕ) :
    Measurable fun p => iv (tOf (Mx m p) i) j := by
  unfold Mx
  simp only [apply_ite (fun M => iv (tOf M i) j)]
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (measurable_iv_mixI measurable_fst measurable_snd m i j) (measurable_iv_mixII m i j)

lemma measurable_Lv (m : ℕ) (i : Fin 3) : Measurable (Lv m i) :=
  measurable_pi_iff.2 fun j => Measurable.ite
    (measurableSet_lt measurable_const (measurable_W m i)) (measurable_ivMx m i j).fst
    measurable_const

lemma measurable_Rv (m : ℕ) (i : Fin 3) : Measurable (Rv m i) :=
  measurable_pi_iff.2 fun j => Measurable.ite
    (measurableSet_lt measurable_const (measurable_W m i)) (measurable_ivMx m i j).snd
    measurable_const

/-- The parameter range `0 < a < 2 < b ≤ m`. -/
def Rng (m : ℕ) : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < 2 ∧ 2 < p.2 ∧ p.2 ≤ m}

lemma measurableSet_Rng (m : ℕ) : MeasurableSet (Rng m) := by
  simp only [Rng, Set.setOf_and]
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))

/-- The kernel as a function: the mixture of the joint mixes of Lemma 1 of the tuples of
Theorem `m:thm:two` (Lemma 3) inside the parameter range, the point mass at `0` outside. -/
def KTfun (m : ℕ) (p : ℝ × ℝ) : Measure (Fin m → ℝ) :=
  if p ∈ Rng m then mixK (W m) (Lv m) (Rv m) p else Measure.dirac 0

lemma measurable_KTfun (m : ℕ) : Measurable (KTfun m) :=
  Measurable.ite (measurableSet_Rng m)
    (measurable_mixK (measurable_W m) (measurable_Lv m) (measurable_Rv m)) measurable_const

/-- The kernel `(a, b) ↦` an `m`-complete mix of `g_{a,b}`. -/
def KT (m : ℕ) : Kernel (ℝ × ℝ) (Fin m → ℝ) := ⟨KTfun m, measurable_KTfun m⟩

lemma Mx_props {m : ℕ} (hm : 3 ≤ m) {a b : ℝ} (ha0 : 0 < a) (ha2 : a < 2) (hb2 : 2 < b)
    (hbm : b ≤ m) : (Mx m (a, b)).Good m b ∧ (∀ x, (Mx m (a, b)).dens m x = g a b x) ∧
      (Mx m (a, b)).length ≤ 3 := by
  unfold Mx; dsimp only
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := thm6_i hm ha0 h hb2 hbm; exact ⟨h1, h2, by omega⟩
  · obtain ⟨-, -, -, h1, h2, h3⟩ := thm6_ii hm (lt_of_not_ge h) ha2 hb2 hbm
    exact ⟨h1, h2, by omega⟩

/-- **The kernel is an `m`-complete mix of `g_{a,b}` with sum `m`**, for `0 < a < 2 < b ≤ m`. -/
theorem KT_spec {m : ℕ} (hm : 3 ≤ m) {a b : ℝ} (ha0 : 0 < a) (ha2 : a < 2) (hb2 : 2 < b)
    (hbm : b ≤ m) :
    IsCompleteMix m (volume.withDensity fun x => ENNReal.ofReal (g a b x)) (KT m (a, b)) ∧
      ∀ᵐ x ∂(KT m (a, b)), ∑ j, x j = (m : ℝ) := by
  obtain ⟨hG, hd, hlen⟩ := Mx_props hm ha0 ha2 hb2 hbm
  have hp : (a, b) ∈ Rng m := ⟨ha0, ha2, hb2, hbm⟩
  have hK : KT m (a, b) = mixK (W m) (Lv m) (Rv m) (a, b) := by
    change KTfun m (a, b) = _; rw [KTfun, if_pos hp]
  have hn : 0 < m := by omega
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hw0 : ∀ i : Fin 3, 0 ≤ W m i (a, b) := fun i => wOf_nonneg hG i
  have hadm : ∀ i : Fin 3, 0 < W m i (a, b) → (tOf (Mx m (a, b)) i).Adm m :=
    fun i h => (adm_of_pos hG h).1
  have hw1 : ∑ i, W m i (a, b) = 1 := by
    rw [← hG.sum_one]
    exact sum_fin_getD (Mx m (a, b)) (0, []) Prod.fst rfl 3 hlen
  have hle : ∀ i j, Lv m i (a, b) j ≤ Rv m i (a, b) j := by
    intro i j; simp only [Lv, Rv]
    split_ifs with h
    · exact adm_le (hadm i h) j
    · norm_num
  have hpoly : ∀ i j, 2 * (Rv m i (a, b) j - Lv m i (a, b) j) ≤
      ∑ j', (Rv m i (a, b) j' - Lv m i (a, b) j') := by
    intro i j
    by_cases h : 0 < W m i (a, b)
    · simp only [Lv, Rv, if_pos h]; exact adm_poly (hadm i h) j
    · simp only [Lv, Rv, if_neg h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      linarith
  have hs : ∀ i, ∑ j, (Lv m i (a, b) j + Rv m i (a, b) j) = 2 * (m : ℝ) := by
    intro i
    by_cases h : 0 < W m i (a, b)
    · simp only [Lv, Rv, if_pos h]; exact adm_mid (hadm i h)
    · simp only [Lv, Rv, if_neg h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
  obtain ⟨h1, h2⟩ := mixK_spec hn hw0 hw1 hle hpoly (m : ℝ) hs
  rw [hK]
  refine ⟨?_, h2⟩
  have step : ∀ i : Fin 3, ENNReal.ofReal (W m i (a, b)) •
      ((m : ℝ≥0∞)⁻¹ • ∑ j, unifI (Lv m i (a, b) j) (Rv m i (a, b) j)) =
      (m : ℝ≥0∞)⁻¹ • (ENNReal.ofReal (wOf (Mx m (a, b)) i) • (tOf (Mx m (a, b)) i).measure) := by
    intro i
    by_cases h : 0 < W m i (a, b)
    · simp only [Lv, Rv, if_pos h]
      rw [sum_unifI_iv (hadm i h).size, smul_comm]; rfl
    · have h0 : ENNReal.ofReal (W m i (a, b)) = 0 := ENNReal.ofReal_eq_zero.2 (not_lt.1 h)
      have h0' : ENNReal.ofReal (wOf (Mx m (a, b)) i) = 0 := h0
      rw [h0, h0', zero_smul, zero_smul, smul_zero]
  have hsum : ∑ i : Fin 3, ENNReal.ofReal (wOf (Mx m (a, b)) i) • (tOf (Mx m (a, b)) i).measure
      = (Mx m (a, b)).measure0 :=
    sum_fin_getD (Mx m (a, b)) (0, []) (fun q => ENNReal.ofReal q.1 • q.2.measure)
      (by simp) 3 hlen
  rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.smul_sum, hsum,
    Mix.measure0_eq _ hG.nonneg (fun p hp h B hB => (((hG.adm p hp h).2) B hB).2.1)] at h1
  have hn' : (0 : ℝ) < m := by exact_mod_cast hn
  have e : (fun x => ENNReal.ofReal (g a b x)) = (m : ℝ≥0∞)⁻¹ •
      fun x => ENNReal.ofReal (((Mx m (a, b)).map fun p => p.1 * p.2.dens x).sum) := by
    funext x
    rw [← hd x, Mix.dens, ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_natCast]
    simp [div_eq_mul_inv, mul_comm]
  rw [e, withDensity_smul _ (Mix.measurable_sum _).ennreal_ofReal]
  exact h1

/-- **`H_twoStepBorel`**: for `m ≥ 3` there is a Markov kernel `(a, b) ↦` an `m`-complete mix of
`g_{a,b}` with sum `m`, for `0 < a < 2 < b ≤ m`. -/
theorem twoStepBorel : AsymThree.H_twoStepBorel := by
  intro m hm
  refine ⟨KT m, ⟨fun p => ?_⟩, fun a b ha0 ha2 hb2 hbm => ?_⟩
  · change IsProbabilityMeasure (KTfun m p)
    unfold KTfun
    split_ifs with hp
    · obtain ⟨ha0, ha2, hb2, hbm⟩ := hp
      have := (KT_spec hm ha0 ha2 hb2 hbm).1.1
      have hK : KT m (p.1, p.2) = mixK (W m) (Lv m) (Rv m) p := by
        change KTfun m p = _; rw [KTfun, if_pos ⟨ha0, ha2, hb2, hbm⟩]
      rw [hK] at this; exact this
    · infer_instance
  · obtain ⟨h1, h2⟩ := KT_spec hm ha0 ha2 hb2 hbm
    exact ⟨fun i => h1.2.2 i, h2⟩

/-! ### Results of `AsymThree` without the hypothesis `H_twoStepBorel` -/

section Unconditional

open AsymThree Set

/-- `AsymThree.three_core` without `H_twoStepBorel`. -/
theorem three_core_tb {m : ℕ} (hm : 3 ≤ m) {u0 v0 : ℝ}
    (hok : ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ v0 → u + v ≤ m ∧ (v ≤ m - 2 ∨ u ≤ m - 2))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ x, x ∂ν = m)
    (hsupp : ν (Icc (m - u0) (m + v0))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin m => unifI 0 2) :=
  three_core twoStepBorel hm hok ν hmean hsupp

/-- `AsymThree.three_scaled` without `H_twoStepBorel`. -/
theorem three_scaled_tb {m : ℕ} (hm : 3 ≤ m) {c H : ℝ} (hH : 0 < H) {u0 v0 : ℝ}
    (hok : ∀ u v : ℝ, 0 < u → u ≤ u0 → 0 < v → v ≤ v0 → u + v ≤ m ∧ (v ≤ m - 2 ∨ u ≤ m - 2))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ x, x ∂ν = m * c)
    (hsupp : ν (Icc (m * c - H * u0) (m * c + H * v0))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin m => unifI (c - H) (c + H)) :=
  three_scaled twoStepBorel hm hH hok ν hmean hsupp

/-- **Proposition `as:prop:three`**, unconditional. -/
theorem prop_three_tb : PropThree := prop_three twoStepBorel

/-- Corollary `as:cor:three` (main statement), with Proposition `as:prop:three` proved;
hypothesis `H_conc_a` kept. -/
theorem cor_three_tb (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνm : ∫ x, x ∂ν = n * ∫ x, x ∂F)
    (hν : ν (Icc (n * ∫ x, x ∂F - (lenThree ⌊q * n⌋₊ H - R) / 2)
      (n * ∫ x, x ∂F + (lenThree ⌊q * n⌋₊ H - R) / 2))ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin n => F) :=
  cor_three' twoStepBorel hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR ν hνm hν

/-- Corollary `as:cor:three`: `F` is `n`-completely mixable (hypothesis `H_conc_a` kept). -/
theorem cor_three_mixable_tb (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (hm3 : 3 ≤ ⌊q * n⌋₊) (hLR : R ≤ lenThree ⌊q * n⌋₊ H) : CompletelyMixable n F :=
  cor_three_mixable' twoStepBorel hC F R hR c H q hH hq0 hq1 hFU n hm3 hLR

/-- Corollary `as:cor:three` (a) (hypothesis `H_conc_a` kept). -/
theorem cor_three_a_tb (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] (R : ℝ) (hR : ∃ a, F (Icc a (a + R))ᶜ = 0) (c H q : ℝ) (hH : 0 < H)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hFU : ENNReal.ofReal q • unifI (c - H) (c + H) ≤ F) (n : ℕ)
    (h4 : 4 ≤ ⌊q * n⌋₊) (hRH : R / H ≤ ⌊q * n⌋₊) : CompletelyMixable n F :=
  cor_three_a' twoStepBorel hC F R hR c H q hH hq0 hq1 hFU n h4 hRH

/-- Corollary `as:cor:three` (b), the theorem of Puccetti, Wang and Wang (hypothesis `H_conc_a`
kept). -/
theorem cor_three_b_tb (hC : H_conc_a) (F : Measure ℝ)
    [IsProbabilityMeasure F] {a b : ℝ} (hab : a < b) (hF : F (Icc a b)ᶜ = 0) (n : ℕ) (hn : 3 ≤ n)
    (hFU : ENNReal.ofReal (3 / n) • unifI a b ≤ F) : CompletelyMixable n F :=
  cor_three_b' twoStepBorel hC F hab hF n hn hFU

/-- Corollary `as:cor:three` (c) (hypothesis `H_conc_a` kept). -/
theorem cor_three_c_tb (hC : H_conc_a) {r : ℕ}
    (F : Fin r → Measure ℝ) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j, ∃ a, F j (Icc a (a + 1))ᶜ = 0) :
    Measure.dirac (3 / 2 + ∑ j, ∫ x, x ∂(F j)) ∈
      aggSet (Sum.elim (fun _ : Σ _k : Fin 1, Fin 3 => unifI 0 1) F) :=
  cor_three_c' twoStepBorel hC F hF

/-- **Remark `as:rem:three`**, unconditional. -/
theorem rem_three_tb (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ x, x ∂ν = 3 / 2)
    (hsupp : (∃ a : ℝ, a ≤ 3 / 2 ∧ 3 / 2 ≤ a + 1 ∧ ν (Icc a (a + 1))ᶜ = 0) ∨
      ν (Icc 1 (5 / 2))ᶜ = 0 ∨ ν (Icc (1 / 2) 2)ᶜ = 0) :
    ν ∈ aggSet (fun _ : Fin 3 => unifI 0 1) :=
  rem_three twoStepBorel ν hmean hsupp

end Unconditional

end Mixes.TwoStepBorel
