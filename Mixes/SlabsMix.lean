import Mixes.Slabs
import Mixes.TwoStepMix

/-!
# Theorem 12 without hypotheses, and Corollary 13

`Mixes.Slabs` proves Theorem 12 (`m:thm:mono`) from two hypotheses: a complete mix `Q₀`
of `U[0, 2]` with sum `n`, and a measurable kernel `κ(a, b)` of complete mixes of `g_{a,b}` with
sum `n`. This file constructs both explicitly and proves Corollary 13 (`m:cor:general`).

## Construction

* `glue`: a finite piecewise definition. Lemma 1 measurably: on the region of tuples where a
  fixed partition `{k} ∪ G ∪ H` of the indices satisfies the triangle inequalities, the vector
  `archVec` of `Mixes.Uniform` with the explicit triangle of `triangle_of_orthonormal`
  is used. `lem1Map` glues these finitely many maps (the choice of the paper, a largest `λ_k`
  and a balanced prefix, shows that every admissible tuple lies in some region); it is jointly
  measurable in the tuple and in `ξ`.
* `K1`: the kernel `(l, r) ↦` (law of `lem1Map (l, r) ξ` under `archPlane`, uniformly permuted),
  Lemmas 1 and 3 for one tuple.
* `KmixS c M`: for a mixture `M` of block tuples (`Mixes.TwoStep`), `∑ c wᵢ K1(τᵢ)`.
* `kappa n`: `(a, b) ↦ KmixS 1 (mix6 n a b)` with `mix6` the mixture of Theorem 6 (`mixI` if
  `a ≤ 1`, `mixII` otherwise). Its measurability in `(a, b)` follows the finitely many cases of
  `mixI` (with `β*` a measurable function into `ℕ`).
* `Q0 n = K1 (0, 2)`: the complete mix of `U[0, 2]`.

## Main results

* `mono_mix`, `mono_completelyMixable`: Theorem 12 without hypotheses.
* `gMeas_eq`: the two definitions of `g_{a,b}` agree (pointwise, for all `a`, `b`).
* `cor13_nonincreasing`, `cor13_nondecreasing`: Corollary 13.

## Differences from the paper

* The permutation in Lemma 3 and the mixture weights are applied as finite sums of measures,
  and the point `ξ` is drawn from `archPlane` (a planar measure with the Archimedes property)
  instead of the sphere; the tuple of Lemma 1 is chosen by the first admissible partition in a
  fixed enumeration rather than by a largest interval and a minimising prefix (any partition
  satisfying the triangle inequalities gives a joint mix).
* Corollary 13: densities are taken right-continuous (non-increasing case) or left-continuous
  (non-decreasing case), as required by `Slabs.exists_nu`; the mean is written as
  `∫ (x - α) f = μ - α` (resp. `∫ (β - x) f = β - μ`) with `α < μ` (resp. `μ < β`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Mixes

namespace SlabsMix

/-! ### Finite piecewise definitions -/

section Glue

variable {X Ω Y : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Y]

open Classical in
/-- `glue d L (x, ω)`: the function `f (x, ω)` of the first pair `(B, f)` of `L` with `x ∈ B`,
and `d (x, ω)` if there is none. -/
def glue (d : X × Ω → Y) : List (Set X × (X × Ω → Y)) → X × Ω → Y
  | [] => d
  | q :: L => fun z => if z.1 ∈ q.1 then q.2 z else glue d L z

lemma measurable_glue {d : X × Ω → Y} (hd : Measurable d) (L : List (Set X × (X × Ω → Y)))
    (hL : ∀ q ∈ L, MeasurableSet q.1 ∧ Measurable q.2) : Measurable (glue d L) := by
  induction L with
  | nil => exact hd
  | cons q L ih =>
    have h := hL q List.mem_cons_self
    exact Measurable.ite (measurable_fst h.1) h.2
      (ih fun q' hq' => hL q' (List.mem_cons_of_mem _ hq'))

omit [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Y] in
lemma glue_spec {d : X × Ω → Y} (L : List (Set X × (X × Ω → Y))) {x : X}
    (h : ∃ q ∈ L, x ∈ q.1) : ∃ q ∈ L, x ∈ q.1 ∧ ∀ ω, glue d L (x, ω) = q.2 (x, ω) := by
  induction L with
  | nil => simp at h
  | cons q L ih =>
    by_cases hx : x ∈ q.1
    · exact ⟨q, List.mem_cons_self, hx, fun ω => by simp [glue, hx]⟩
    · obtain ⟨q', hq', hxq'⟩ := h
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact absurd hxq' hx
      obtain ⟨q'', h1, h2, h3⟩ := ih ⟨q', hq', hxq'⟩
      exact ⟨q'', List.mem_cons_of_mem _ h1, h2, fun ω => by simp [glue, hx, h3]⟩

end Glue

/-! ### Lemma 1 with measurable dependence on the tuple -/

section Lemma1

variable {n : ℕ}

/-- The plane of `archPlane`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The orthonormal pair of the plane. -/
def eu : E2 := EuclideanSpace.single 0 1
/-- The orthonormal pair of the plane. -/
def ew : E2 := EuclideanSpace.single 1 1

/-- Discrete data of Lemma 1: an index `k` and two sets `G`, `H`. -/
abbrev Part (n : ℕ) := Fin n × Finset (Fin n) × Finset (Fin n)

/-- `{k}`, `G`, `H` partition the indices. -/
def Part.OK (d : Part n) : Prop :=
  d.1 ∉ d.2.1 ∧ d.1 ∉ d.2.2 ∧ Disjoint d.2.1 d.2.2 ∧ ∀ j, j = d.1 ∨ j ∈ d.2.1 ∨ j ∈ d.2.2

/-- `λ_k` for the tuple `x = (l, r)`. -/
def lamK (d : Part n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := x.2 d.1 - x.1 d.1
/-- `S = ∑_{j ∈ G} λ_j`. -/
def sumG (d : Part n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := ∑ j ∈ d.2.1, (x.2 j - x.1 j)
/-- `T = ∑_{j ∈ H} λ_j`. -/
def sumH (d : Part n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := ∑ j ∈ d.2.2, (x.2 j - x.1 j)

/-- The region where the partition `d` gives a triangle: `0 < λ_k`, `|S - T| ≤ λ_k ≤ S + T`. -/
def region (d : Part n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {x | d.OK ∧ 0 < lamK d x ∧ |sumG d x - sumH d x| ≤ lamK d x ∧ lamK d x ≤ sumG d x + sumH d x}

/-- The abscissa of the triangle (as in `triangle_of_orthonormal`). -/
def triX (d : Part n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (lamK d x ^ 2 + sumH d x ^ 2 - sumG d x ^ 2) / (2 * lamK d x)
/-- The ordinate of the triangle. -/
def triY (d : Part n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := √(sumH d x ^ 2 - triX d x ^ 2)

/-- The vector of Lemma 1 for the partition `d`, with the explicit triangle. -/
def archD (d : Part n) (z : ((Fin n → ℝ) × (Fin n → ℝ)) × E2) : Fin n → ℝ :=
  archVec z.1.1 z.1.2 d.1 d.2.1 d.2.2 (lamK d z.1 • eu)
    ((triX d z.1 - lamK d z.1) • eu + triY d z.1 • ew) (-(triX d z.1 • eu + triY d z.1 • ew)) z.2

lemma measurableSet_region (d : Part n) : MeasurableSet (region d) := by
  have h1 : Measurable (lamK d) := by unfold lamK; fun_prop
  have h2 : Measurable (sumG d) := by unfold sumG; fun_prop
  have h3 : Measurable (sumH d) := by unfold sumH; fun_prop
  unfold region; simp only [ofPred_and]
  exact (MeasurableSet.const d.OK).inter <|
    (measurableSet_lt (f := fun _ => (0:ℝ)) measurable_const h1).inter <|
      (measurableSet_le (f := fun x => |sumG d x - sumH d x|) ((h2.sub h3).abs) h1).inter
        (measurableSet_le (g := fun x => sumG d x + sumH d x) h1 (h2.add h3))

lemma measurable_archD (d : Part n) : Measurable (archD d) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold archD archVec triY triX lamK sumG sumH
  split_ifs <;> fun_prop

/-- The list of all partitions with their regions and maps. -/
def lem1List (n : ℕ) :
    List (Set ((Fin n → ℝ) × (Fin n → ℝ)) × (((Fin n → ℝ) × (Fin n → ℝ)) × E2 → Fin n → ℝ)) :=
  (Finset.univ : Finset (Part n)).toList.map fun d => (region d, archD d)

/-- The vector of Lemma 1, glued over all partitions (`0` outside the regions). -/
def lem1Map (n : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) × E2 → Fin n → ℝ :=
  glue (fun _ => 0) (lem1List n)

lemma measurable_lem1Map (n : ℕ) : Measurable (lem1Map n) := by
  refine measurable_glue measurable_const _ fun q hq => ?_
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hq
  exact ⟨measurableSet_region d, measurable_archD d⟩


/-- Every admissible tuple lies in the region of some partition: the choices of Lemma 1 (a
largest length, an enumeration of the other indices, a balanced prefix) give one. -/
lemma exists_region (τ : Admissible n) : ∃ d : Part n, (τ.l, τ.r) ∈ region d := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    obtain ⟨j, -⟩ := τ.pos; exact ⟨j, Finset.mem_univ j⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => τ.r j - τ.l j) hne
  set L := (Finset.univ.erase k).toList
  have hL : L.Nodup := Finset.nodup_toList _
  have hLk : ∀ j, j ∈ L ↔ j ≠ k := fun j => by simp [L]
  let g : ℕ → ℝ := fun s' => |2 * ((L.take s').map fun j => τ.r j - τ.l j).sum -
    ∑ j ∈ Finset.univ.erase k, (τ.r j - τ.l j)|
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (Finset.range (L.length + 1)) g
    ⟨0, by simp⟩
  have hs' : s ≤ L.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  obtain ⟨hbal, htri, -⟩ := lem_arch isArchimedesMeasure_archPlane orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 τ.l τ.r τ.le τ.pos
    τ.polygon k (fun j => hk j (Finset.mem_univ j)) L hL hLk s hs'
    (fun s' hs'' => hmin s' (Finset.mem_range.2 (Nat.lt_succ_of_le hs'')))
  have hdisj := List.disjoint_take_drop hL (le_refl s)
  refine ⟨(k, (L.take s).toFinset, (L.drop s).toFinset), ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hbal, htri⟩⟩
  · intro h; exact (hLk k).1 (List.mem_of_mem_take (List.mem_toFinset.1 h)) rfl
  · intro h; exact (hLk k).1 (List.mem_of_mem_drop (List.mem_toFinset.1 h)) rfl
  · exact Finset.disjoint_left.2 fun j h1 h2 =>
      hdisj (List.mem_toFinset.1 h1) (List.mem_toFinset.1 h2)
  · intro j
    by_cases hj : j = k
    · exact Or.inl hj
    · right
      have : j ∈ L.take s ++ L.drop s := by rw [List.take_append_drop]; exact (hLk j).2 hj
      rcases List.mem_append.1 this with h | h
      · exact Or.inl (List.mem_toFinset.2 h)
      · exact Or.inr (List.mem_toFinset.2 h)
  · obtain ⟨j, hj⟩ := τ.pos
    exact lt_of_lt_of_le (sub_pos.2 hj) (hk j (Finset.mem_univ j))

/-- **Lemma 1** with the measurable vector `lem1Map`: for an admissible tuple, the law of
`ξ ↦ lem1Map ((l, r), ξ)` under `archPlane` is a joint mix of the `U[l_j, r_j]` with sum `n`. -/
theorem lem1Map_jointMix (τ : Admissible n) :
    IsJointMix (fun j => unifI (τ.l j) (τ.r j)) (archPlane.map fun ξ => lem1Map n ((τ.l, τ.r), ξ))
      ∧ ∀ᵐ x ∂(archPlane.map fun ξ => lem1Map n ((τ.l, τ.r), ξ)), ∑ j, x j = (n : ℝ) := by
  obtain ⟨d, hd⟩ := exists_region τ
  obtain ⟨q, hq, hxq, hglue⟩ := glue_spec (d := fun _ => (0 : Fin n → ℝ)) (lem1List n)
    ⟨(region d, archD d), List.mem_map.2 ⟨d, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩, hd⟩
  obtain ⟨d', -, rfl⟩ := List.mem_map.1 hq
  have hfun : (fun ξ => lem1Map n ((τ.l, τ.r), ξ)) = fun ξ => archD d' ((τ.l, τ.r), ξ) :=
    funext hglue
  obtain ⟨⟨hkG, hkH, hGH, hcov⟩, hpos, h1, h2⟩ := hxq
  have hS : 0 ≤ sumG d' (τ.l, τ.r) := Finset.sum_nonneg fun j _ => sub_nonneg.2 (τ.le j)
  have hT : 0 ≤ sumH d' (τ.l, τ.r) := Finset.sum_nonneg fun j _ => sub_nonneg.2 (τ.le j)
  obtain ⟨hEk, hEG, hEH, hsum⟩ := triangle_of_orthonormal orthonormal_single_two.1
    orthonormal_single_two.2.1 orthonormal_single_two.2.2 hpos hS hT h1 h2
  obtain ⟨hP, hc⟩ := arch_of_partition isArchimedesMeasure_archPlane τ.l τ.r τ.le d'.1 d'.2.1
    d'.2.2 hkG hkH hGH hcov _ _ _ hEk hEG hEH hsum
  rw [hfun]
  refine ⟨hP, hc.mono fun x hx => ?_⟩
  rw [hx, τ.mid]; ring

instance : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1

/-- The measure of Lemmas 1 and 3 for one tuple `(l, r)`: the law of `lem1Map ((l, r), ξ)`,
`ξ ∼ archPlane`, with its coordinates permuted uniformly at random. -/
def K1fun (n : ℕ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  permAvg (archPlane.map fun ξ => lem1Map n (x, ξ))

lemma measurable_K1fun (n : ℕ) : Measurable (K1fun n) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hm : ∀ x, Measurable fun ξ => lem1Map n (x, ξ) := fun x =>
    (measurable_lem1Map n).comp measurable_prodMk_left
  have : ∀ (π : Equiv.Perm (Fin n)) x,
      ((archPlane.map fun ξ => lem1Map n (x, ξ)).map fun y => y ∘ π) s =
        archPlane (Prod.mk x ⁻¹' ((fun z => lem1Map n z ∘ π) ⁻¹' s)) := by
    intro π x
    rw [Measure.map_apply (measurable_comp_perm π) hs,
      Measure.map_apply (hm x) (measurable_comp_perm π hs)]
    rfl
  simp only [K1fun, permAvg, sum_apply, smul_apply, smul_eq_mul, this]
  refine Measurable.const_mul (Finset.measurable_sum _ fun π _ => ?_) _
  exact measurable_measure_prodMk_left
    (((measurable_comp_perm π).comp (measurable_lem1Map n)) hs)

/-- The kernel `(l, r) ↦ K1fun n (l, r)`. -/
def K1 (n : ℕ) : Kernel ((Fin n → ℝ) × (Fin n → ℝ)) (Fin n → ℝ) :=
  ⟨K1fun n, measurable_K1fun n⟩

lemma K1_apply (x : (Fin n → ℝ) × (Fin n → ℝ)) : K1 n x = K1fun n x := rfl

/-- **Lemmas 1 and 3** for one admissible tuple, with the kernel `K1`: `K1 n (l, r)` is an
`n`-complete mix of the marginal `m_τ` with sum `n`. -/
theorem K1_spec (τ : Admissible n) :
    IsCompleteMix n τ.marginal (K1 n (τ.l, τ.r)) ∧
      ∀ᵐ x ∂(K1 n (τ.l, τ.r)), ∑ j, x j = (n : ℝ) := by
  obtain ⟨hP, hc⟩ := lem1Map_jointMix τ
  have h := lem_sym (ι := Unit) (fun _ => 1) (by simp) (fun _ j => unifI (τ.l j) (τ.r j))
    (fun _ => archPlane.map fun ξ => lem1Map n ((τ.l, τ.r), ξ)) n (fun _ => hP) (fun _ => hc)
  simpa [mixture, Admissible.marginal, K1_apply, K1fun] using h

end Lemma1


/-! ### Mixtures of block tuples -/

section Mix

open TwoStep

variable {n : ℕ}

/-- The left ends of the `n` intervals of a block tuple (`0` beyond its size). -/
def eL (n : ℕ) (t : Tup) : Fin n → ℝ := fun j => (t.expand.getD j (0, 0)).1

/-- The right ends of the `n` intervals of a block tuple (`0` beyond its size). -/
def eR (n : ℕ) (t : Tup) : Fin n → ℝ := fun j => (t.expand.getD j (0, 0)).2

/-- The output of Lemmas 1 and 3 for a mixture `M = ∑ wᵢ τᵢ` of block tuples, with the weights
multiplied by `c`: `∑ᵢ (c wᵢ) K1(τᵢ)`. -/
def KmixS (n : ℕ) (c : ℝ) (M : Mix) : Measure (Fin n → ℝ) :=
  (M.map fun q => ENNReal.ofReal (c * q.1) • K1 n (eL n q.2, eR n q.2)).sum

lemma eLR_toAdmissible (t : Tup) (h : t.Adm n) :
    eL n t = (t.toAdmissible h).l ∧ eR n t = (t.toAdmissible h).r := by
  have hlen : t.expand.length = n := by rw [Tup.length_expand, h.size]
  constructor <;> funext j <;>
  · have hj : (j : ℕ) < t.expand.length := by rw [hlen]; exact j.isLt
    simp [eL, eR, Tup.toAdmissible, List.getElem?_eq_getElem hj]

lemma KmixS_nil (c : ℝ) : KmixS n c [] = 0 := by simp [KmixS]

lemma KmixS_cons (c : ℝ) (q : ℝ × Tup) (M : Mix) :
    KmixS n c (q :: M) = ENNReal.ofReal (c * q.1) • K1 n (eL n q.2, eR n q.2) + KmixS n c M := by
  simp [KmixS]

lemma KmixS_map (c d : ℝ) (M : Mix) :
    KmixS n c (M.map fun q => (d * q.1, q.2)) = KmixS n (c * d) M := by
  simp only [KmixS, List.map_map]
  congr 2
  funext q
  simp [mul_assoc]

/-- The marginals, the sum and the total mass of `KmixS n 1 M`. -/
lemma KmixS_one_spec (M : Mix) (hw : ∀ q ∈ M, 0 ≤ q.1) (hadm : ∀ q ∈ M, 0 < q.1 → q.2.Adm n) :
    (∀ j, (KmixS n 1 M).map (fun x => x j) = (n : ℝ≥0∞)⁻¹ • M.measure0) ∧
      KmixS n 1 M {x | ∑ j, x j = (n : ℝ)}ᶜ = 0 ∧
      KmixS n 1 M univ = ENNReal.ofReal (M.map Prod.fst).sum := by
  induction M with
  | nil => simp [KmixS_nil, Mix.measure0]
  | cons q M ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun q' hq' => hw q' (List.mem_cons_of_mem _ hq'))
      (fun q' hq' => hadm q' (List.mem_cons_of_mem _ hq'))
    have hq0 := hw q List.mem_cons_self
    have hrest : 0 ≤ (M.map Prod.fst).sum := List.sum_nonneg (by
      simp only [List.mem_map]
      rintro _ ⟨q', hq', rfl⟩
      exact hw q' (List.mem_cons_of_mem _ hq'))
    simp only [KmixS_cons, one_mul, Mix.measure0, List.map_cons, List.sum_cons] at ih1 ⊢
    rcases hq0.lt_or_eq with hq | hq
    · have hA := hadm q List.mem_cons_self hq
      obtain ⟨hl, hr⟩ := eLR_toAdmissible q.2 hA
      obtain ⟨⟨hprob, -, hmarg⟩, hsum⟩ := K1_spec (q.2.toAdmissible hA)
      rw [← hl, ← hr] at hprob hmarg hsum
      refine ⟨fun j => ?_, ?_, ?_⟩
      · rw [Measure.map_add _ _ (measurable_pi_apply j),
          Measure.map_smul _ (measurable_pi_apply j).aemeasurable, hmarg j, ih1 j,
          Tup.marginal_toAdmissible, smul_add, smul_comm]
      · have h0 : K1 n (eL n q.2, eR n q.2) {x | ∑ j, x j = (n : ℝ)}ᶜ = 0 := by
          rw [ae_iff] at hsum; simpa [Set.compl_def] using hsum
        rw [add_apply, smul_apply, ih2, h0]
        simp
      · rw [add_apply, smul_apply, ih3, measure_univ, smul_eq_mul, mul_one,
          ENNReal.ofReal_add hq0 hrest]
    · rw [← hq]
      simpa using ⟨ih1, ih2, ih3⟩

/-- **Lemma 3 for the mixtures of Theorem 6**: if `M` is a good mixture of block tuples whose
marginal density is `f`, then `KmixS n 1 M` is an `n`-complete mix of the distribution with
density `f`, with sum `n`. -/
theorem KmixS_spec {M : Mix} {b : ℝ} (hn : 0 < n) (hM : M.Good n b) {f : ℝ → ℝ}
    (hf : ∀ x, M.dens n x = f x) :
    IsCompleteMix n (volume.withDensity fun x => ENNReal.ofReal (f x)) (KmixS n 1 M) ∧
      ∀ᵐ x ∂(KmixS n 1 M), ∑ j, x j = (n : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := KmixS_one_spec (n := n) M hM.nonneg (fun p hp h => (hM.adm p hp h).1)
  have hmarg : (n : ℝ≥0∞)⁻¹ • M.measure0 = volume.withDensity fun x => ENNReal.ofReal (f x) := by
    rw [Mix.measure0_eq M hM.nonneg (fun p hp h B hB => (((hM.adm p hp h).2) B hB).2.1)]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e : (fun x => ENNReal.ofReal (f x)) = (n : ENNReal)⁻¹ •
        fun x => ENNReal.ofReal ((M.map fun p => p.1 * p.2.dens x).sum) := by
      funext x
      rw [← hf x, Mix.dens, ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_natCast]
      simp [div_eq_mul_inv, mul_comm]
    rw [e, withDensity_smul _ (Mix.measurable_sum M).ennreal_ofReal]
  have hsum : ∀ᵐ x ∂(KmixS n 1 M), ∑ j, x j = (n : ℝ) := by
    rw [ae_iff]; simpa [Set.compl_def] using h2
  refine ⟨⟨⟨by rw [h3, hM.sum_one, ENNReal.ofReal_one]⟩, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  rw [h1 j, hmarg]

end Mix


/-! ### Measurable dependence on the parameters -/

section Meas

open TwoStep

variable {P : Type*} [MeasurableSpace P] {n : ℕ}

/-- A block tuple whose ends depend on a parameter `p`, with fixed multiplicities. -/
def tmpl (T : List (ℕ × (P → ℝ) × (P → ℝ))) (p : P) : Tup :=
  T.map fun q => ⟨q.1, q.2.1 p, q.2.2 p⟩

lemma measurable_getD_tmpl (T : List (ℕ × (P → ℝ) × (P → ℝ)))
    (hT : ∀ q ∈ T, Measurable q.2.1 ∧ Measurable q.2.2) (j : ℕ) :
    Measurable fun p => (Tup.expand (tmpl T p)).getD j (0, 0) := by
  induction T generalizing j with
  | nil => simp [tmpl, Tup.expand]
  | cons q T ih =>
    have e : ∀ p, Tup.expand (tmpl (q :: T) p) =
        List.replicate q.1 (q.2.1 p, q.2.2 p) ++ Tup.expand (tmpl T p) := fun p => by
      simp [tmpl, Tup.expand]
    simp_rw [e]
    have hq := hT q List.mem_cons_self
    by_cases hj : j < q.1
    · have : ∀ p, (List.replicate q.1 (q.2.1 p, q.2.2 p) ++ Tup.expand (tmpl T p)).getD j (0, 0)
          = (q.2.1 p, q.2.2 p) := fun p => by
        rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_replicate _ hj]
      simp_rw [this]; exact hq.1.prodMk hq.2
    · have : ∀ p, (List.replicate q.1 (q.2.1 p, q.2.2 p) ++ Tup.expand (tmpl T p)).getD j (0, 0)
          = (Tup.expand (tmpl T p)).getD (j - q.1) (0, 0) := fun p => by
        rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp
      simp_rw [this]
      exact ih (fun q' hq' => hT q' (List.mem_cons_of_mem _ hq')) _

lemma measurable_eLR_tmpl (T : List (ℕ × (P → ℝ) × (P → ℝ)))
    (hT : ∀ q ∈ T, Measurable q.2.1 ∧ Measurable q.2.2) :
    Measurable fun p => (eL n (tmpl T p), eR n (tmpl T p)) :=
  (measurable_pi_iff.2 fun j : Fin n => (measurable_getD_tmpl T hT (j : ℕ)).fst).prodMk
    (measurable_pi_iff.2 fun j : Fin n => (measurable_getD_tmpl T hT (j : ℕ)).snd)

/-- A family of mixtures whose `KmixS` depends measurably on the parameter, for every
measurable factor `c` of the weights. -/
def MeasFam (n : ℕ) (M : P → Mix) : Prop :=
  ∀ c : P → ℝ, Measurable c → ∀ s, MeasurableSet s → Measurable fun p => KmixS n (c p) (M p) s

lemma measFam_nil : MeasFam n (fun _ : P => ([] : Mix)) := by
  intro c _ s _; simp only [KmixS_nil, zero_apply]; exact measurable_const

lemma measFam_cons {w : P → ℝ} {t : P → Tup} {M : P → Mix} (hw : Measurable w)
    (ht : Measurable fun p => (eL n (t p), eR n (t p))) (hM : MeasFam n M) :
    MeasFam n (fun p => (w p, t p) :: M p) := by
  intro c hc s hs
  simp only [KmixS_cons, add_apply, smul_apply, smul_eq_mul]
  exact ((hc.mul hw).ennreal_ofReal.mul ((Kernel.measurable_coe (K1 n) hs).comp ht)).add
    (hM c hc s hs)

lemma measFam_tmpl_cons {w : P → ℝ} (T : List (ℕ × (P → ℝ) × (P → ℝ))) {M : P → Mix}
    (hw : Measurable w) (hT : ∀ q ∈ T, Measurable q.2.1 ∧ Measurable q.2.2) (hM : MeasFam n M) :
    MeasFam n (fun p => (w p, tmpl T p) :: M p) :=
  measFam_cons hw (measurable_eLR_tmpl T hT) hM

lemma measFam_ite {C : P → Prop} [DecidablePred C] {M₁ M₂ : P → Mix}
    (hC : MeasurableSet {p | C p}) (h₁ : MeasFam n M₁) (h₂ : MeasFam n M₂) :
    MeasFam n (fun p => if C p then M₁ p else M₂ p) := by
  intro c hc s hs
  have : (fun p => KmixS n (c p) (if C p then M₁ p else M₂ p) s) =
      fun p => if C p then KmixS n (c p) (M₁ p) s else KmixS n (c p) (M₂ p) s := by
    funext p; split_ifs <;> rfl
  rw [this]; exact Measurable.ite hC (h₁ c hc s hs) (h₂ c hc s hs)

lemma measFam_nat {β : P → ℕ} (hβ : Measurable β) (M : ℕ → P → Mix) (hM : ∀ k, MeasFam n (M k)) :
    MeasFam n (fun p => M (β p) p) := by
  intro c hc s hs
  have hF : Measurable fun z : P × ℕ => KmixS n (c z.1) (M z.2 z.1) s := by
    apply measurable_from_prod_countable_left
    intro k
    exact hM k c hc s hs
  have hg : Measurable fun p => (p, β p) := measurable_id.prodMk hβ
  have := hF.comp hg
  simp only [Function.comp_def] at this
  exact this

lemma measFam_map {M : P → Mix} {d : P → ℝ} (hM : MeasFam n M) (hd : Measurable d) :
    MeasFam n (fun p => (M p).map fun q => (d p * q.1, q.2)) := by
  intro c hc s hs
  simp only [KmixS_map]
  exact hM _ (hc.mul hd) s hs

lemma measurable_findGreatest {Q : P → ℕ → Prop} [∀ p, DecidablePred (Q p)]
    (hQ : ∀ k, MeasurableSet {p | Q p k}) (N : ℕ) :
    Measurable fun p => Nat.findGreatest (Q p) N := by
  induction N with
  | zero => simp only [Nat.findGreatest_zero]; exact measurable_const
  | succ N ih =>
    simp_rw [Nat.findGreatest_succ]
    exact Measurable.ite (hQ (N + 1)) measurable_const ih

/-- The mixture of Theorem 6 (i) depends measurably on `(a, b)`. -/
lemma measFam_mixI {f : P → ℝ × ℝ} (hf : Measurable f) :
    MeasFam n (fun p => mixI n (f p).1 (f p).2) := by
  have ha : Measurable fun p => (f p).1 := measurable_fst.comp hf
  have hb : Measurable fun p => (f p).2 := measurable_snd.comp hf
  have hu : ∀ β, Measurable fun p => u n (f p).1 (f p).2 β := fun β => by unfold u; fun_prop
  have hS : ∀ β, MeasFam n (fun p => S n (f p).1 (f p).2 β) := fun β => by
    refine measFam_tmpl_cons [(n - 1 - β, fun _ => 0, fun p => (f p).1),
      (β - 1, fun _ => 0, fun p => (f p).2), (1, fun p => (f p).1, fun p => (f p).2),
      (1, fun _ => 0, fun p => u n (f p).1 (f p).2 β)] ((hu β).div hb) ?_ <|
      measFam_tmpl_cons [(n - β, fun _ => 0, fun p => (f p).1),
        (β - 1, fun _ => 0, fun p => (f p).2), (1, fun p => u n (f p).1 (f p).2 β,
        fun p => (f p).2)] (measurable_const.sub ((hu β).div hb)) ?_ measFam_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl) <;> exact ⟨by fun_prop, by fun_prop⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl) <;> exact ⟨by fun_prop, by fun_prop⟩
  have hSD : MeasFam n (fun p => SD n (f p).1 (f p).2) := by
    refine measFam_tmpl_cons [(n - 2, fun _ => 0, fun p => (f p).1),
      (2, fun p => u n (f p).1 (f p).2 2 / 2, fun p => (f p).2)]
      (measurable_const.sub ((hu 2).div hb)) ?_ <|
      measFam_tmpl_cons [(n - 3, fun _ => 0, fun p => (f p).1),
        (1, fun _ => 0, fun p => u n (f p).1 (f p).2 2 / 2),
        (1, fun p => (f p).1, fun p => (f p).2),
        (1, fun p => u n (f p).1 (f p).2 2 / 2, fun p => (f p).2)] ((hu 2).div hb) ?_ measFam_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl) <;> exact ⟨by fun_prop, by fun_prop⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl | rfl | rfl) <;> exact ⟨by fun_prop, by fun_prop⟩
  have hβ : Measurable fun p => betaStar n (f p).1 (f p).2 :=
    measurable_findGreatest (Q := fun p β => 0 ≤ u n (f p).1 (f p).2 β)
      (fun k => measurableSet_le measurable_const (hu k)) (n - 1)
  unfold mixI
  refine measFam_ite (measurableSet_le (hu 1) hb) (hS 1) <|
    measFam_ite ?_ (measFam_nat hβ (fun β p => S n (f p).1 (f p).2 β) hS) <|
      measFam_ite (measurableSet_le (hu 2) (measurable_const.mul ha)) (hS 2) hSD
  simp only [ofPred_and]
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (hu 3))

/-- The mixture of Theorem 6: part (i) for `a ≤ 1`, part (ii) otherwise. -/
def mix6 (n : ℕ) (a b : ℝ) : Mix := if a ≤ 1 then mixI n a b else mixII n a b

lemma measFam_mix6 {f : P → ℝ × ℝ} (hf : Measurable f) :
    MeasFam n (fun p => mix6 n (f p).1 (f p).2) := by
  have ha : Measurable fun p => (f p).1 := measurable_fst.comp hf
  have hb : Measurable fun p => (f p).2 := measurable_snd.comp hf
  have hθ : Measurable fun p => theta (f p).1 (f p).2 := by unfold theta; fun_prop
  unfold mix6 mixII
  refine measFam_ite (measurableSet_le ha measurable_const) (measFam_mixI hf) <|
    measFam_tmpl_cons [(n, fun p => 2 - (f p).1, fun p => (f p).1)] hθ ?_ <|
      measFam_map (measFam_mixI (f := fun p => (2 - (f p).1, (f p).2)) (by fun_prop))
        (measurable_const.sub hθ)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro q rfl; exact ⟨by fun_prop, by fun_prop⟩

end Meas


/-! ### The kernel `κ`, the complete mix `Q₀`, and Theorem 12 -/

section Thm12

open TwoStep

/-- The kernel of complete mixes of `g_{a,b}`: Theorem 6 (`mix6`), then Lemmas 1 and 3
(`KmixS`). -/
def kappa (n : ℕ) : Kernel (ℝ × ℝ) (Fin n → ℝ) :=
  ⟨fun p => KmixS n 1 (mix6 n p.1 p.2), Measure.measurable_of_measurable_coe _ fun s hs =>
    measFam_mix6 (n := n) measurable_id (fun _ => 1) measurable_const s hs⟩

lemma kappa_apply (n : ℕ) (a b : ℝ) : kappa n (a, b) = KmixS n 1 (mix6 n a b) := rfl

/-- **Theorem 6 with Lemmas 1 and 3, measurably**: for `n ≥ 3` and `0 < a < 2 < b ≤ n`,
`kappa n (a, b)` is an `n`-complete mix of the distribution with density `g_{a,b}`, with sum
`n`. -/
theorem kappa_spec {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (ha0 : 0 < a) (ha2 : a < 2) (hb2 : 2 < b)
    (hbn : b ≤ n) :
    IsCompleteMix n (volume.withDensity fun x => ENNReal.ofReal (TwoStep.g a b x)) (kappa n (a, b))
      ∧ ∀ᵐ x ∂(kappa n (a, b)), ∑ j, x j = (n : ℝ) := by
  rw [kappa_apply, mix6]
  split_ifs with ha1
  · obtain ⟨hG, hd, -⟩ := thm6_i hn ha0 ha1 hb2 hbn
    exact KmixS_spec (by omega) hG hd
  · obtain ⟨-, -, -, hG, hd, -⟩ := thm6_ii hn (lt_of_not_ge ha1) ha2 hb2 hbn
    exact KmixS_spec (by omega) hG hd

/-- The two definitions of `g_{a,b}` (`Mixes.Slabs` and `Mixes.TwoStep`)
agree at every point, for all `a`, `b`. -/
lemma slabs_g_eq (a b x : ℝ) : Slabs.g a b x = TwoStep.g a b x := by
  simp only [Slabs.g, TwoStep.g, Set.indicator, Set.mem_Ico, Slabs.h1, TwoStep.h1, Slabs.h2,
    TwoStep.h2]
  split_ifs <;> simp_all; linarith

/-- The two distributions with density `g_{a,b}` agree. -/
lemma gMeas_eq (a b : ℝ) :
    Slabs.gMeas a b = volume.withDensity fun x => ENNReal.ofReal (TwoStep.g a b x) := by
  simp only [Slabs.gMeas, slabs_g_eq]

/-- The admissible tuple `n · [0, 2]` (`n ≥ 2`). -/
def tauZero (n : ℕ) (hn : 2 ≤ n) : Admissible n where
  l _ := 0
  r _ := 2
  le _ := by norm_num
  pos := ⟨⟨0, by omega⟩, by norm_num⟩
  polygon _ := by
    simp only [sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  mid := by simp [mul_comm]

/-- The complete mix of `U[0, 2]`: Lemmas 1 and 3 for the tuple `n · [0, 2]`. -/
def Q0 (n : ℕ) : Measure (Fin n → ℝ) := K1 n (fun _ => 0, fun _ => 2)

/-- `Q0 n` is an `n`-complete mix of `U[0, 2]` with sum `n`, for `n ≥ 2`. -/
theorem Q0_spec {n : ℕ} (hn : 2 ≤ n) :
    IsCompleteMix n (unifI 0 2) (Q0 n) ∧ ∀ᵐ x ∂(Q0 n), ∑ j, x j = (n : ℝ) := by
  have h := K1_spec (tauZero n hn)
  have hm : (tauZero n hn).marginal = unifI 0 2 := by
    simp only [Admissible.marginal, tauZero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
      ENNReal.inv_mul_cancel (by simp; omega) (ENNReal.natCast_ne_top n), one_smul]
  rw [hm] at h
  exact h


lemma three_le_of {n : ℕ} {b : ℝ} (hb2 : 2 < b) (hbn : b ≤ n) : 3 ≤ n := by
  have : (2 : ℝ) < n := hb2.trans_le hbn
  exact_mod_cast (show 2 < n by exact_mod_cast this)

variable {f : ℝ → ℝ} {ν : Measure ℝ}

/-- **Theorem 12** (`m:thm:mono`) without hypotheses. Let `n ≥ 2` and let `f` be a probability
density on `(0, ∞)` with mean `1` that vanishes on `[B, ∞)` with `B ≤ n`, given through a
measure `ν` with `ν((-∞, 0]) = 0` and `ν((x, ∞)) = f(x)` for `x > 0` (for non-increasing
right-continuous `f`, `Slabs.exists_nu` constructs `ν`). Then the output of Algorithm 11,
`algMix (slab ν) (Q0 n) (kappa n)`, with the explicit complete mix `Q0 n` of `U[0, 2]` and the
explicit measurable kernel `kappa n` of complete mixes of `g_{a,b}`, is an `n`-complete mix of
the distribution with density `f`, with sum `n`. -/
theorem mono_mix {n : ℕ} (hn : 2 ≤ n) [SFinite ν] (hν0 : ν (Iic 0) = 0)
    (hνf : ∀ x, 0 < x → ν (Ioi x) = ENNReal.ofReal (f x)) {B : ℝ} (hBn : B ≤ n)
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1)
    (hmean1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) = 1) :
    IsCompleteMix n (Slabs.densMeas f) (Slabs.algMix (Slabs.slab ν) (Q0 n) (kappa n)) ∧
      ∀ᵐ x ∂(Slabs.algMix (Slabs.slab ν) (Q0 n) (kappa n)), ∑ j, x j = (n : ℝ) :=
  Slabs.mono_mix hn hν0 hνf hBn hB hf1 hmean1 (Q0 n) (Q0_spec hn).2 (Q0_spec hn).1.2.2 (kappa n)
    (fun _ _ ha0 ha2 hb2 hbn => (kappa_spec (three_le_of hb2 hbn) ha0 ha2 hb2 hbn).2)
    (fun a b ha0 ha2 hb2 hbn j => by
      rw [gMeas_eq]; exact (kappa_spec (three_le_of hb2 hbn) ha0 ha2 hb2 hbn).1.2.2 j)

/-- **Theorem 12** for a non-increasing, right-continuous probability density `f` on `(0, ∞)`
with mean `1` vanishing on `[B, ∞)`, `B ≤ n`, `n ≥ 2`: the distribution with density `f` has an
`n`-complete mix with sum `n`. No hypotheses beyond the paper's (and right-continuity). -/
theorem mono_completelyMixable {n : ℕ} (hn : 2 ≤ n) (hmono : AntitoneOn f (Ioi 0))
    (hrc : ∀ x, 0 < x → ContinuousWithinAt f (Ici x) x) {B : ℝ} (hBn : B ≤ n)
    (hB : ∀ x, B ≤ x → f x = 0) (hf1 : ∫⁻ x in Ioi 0, ENNReal.ofReal (f x) = 1)
    (hmean1 : ∫⁻ x in Ioi 0, ENNReal.ofReal x * ENNReal.ofReal (f x) = 1) :
    ∃ Q : Measure (Fin n → ℝ), IsCompleteMix n (Slabs.densMeas f) Q ∧
      ∀ᵐ x ∂Q, ∑ j, x j = (n : ℝ) := by
  obtain ⟨ν, hνs, hν0, hνf⟩ := Slabs.exists_nu hmono hrc hB
  exact ⟨_, mono_mix hn hν0 hνf hBn hB hf1 hmean1⟩

end Thm12


/-! ### Corollary 13: affine rescaling and reflection -/

section Cor13

variable {n : ℕ}

/-- An affine image of a complete mix: if `Q` is an `n`-complete mix of `μ` with sum `s`, then
the law of `(α + c X_j)_j` is an `n`-complete mix of the law of `α + c X` with sum
`n α + c s`. -/
theorem isCompleteMix_affine {μ : Measure ℝ} {Q : Measure (Fin n → ℝ)} {s : ℝ}
    (hQ : IsCompleteMix n μ Q) (hs : ∀ᵐ x ∂Q, ∑ j, x j = s) (α c : ℝ) :
    IsCompleteMix n (μ.map fun y => α + c * y) (Q.map fun x j => α + c * x j) ∧
      ∀ᵐ x ∂(Q.map fun x j => α + c * x j), ∑ j, x j = n * α + c * s := by
  obtain ⟨hprob, -, hmarg⟩ := hQ
  have hA : Measurable fun x : Fin n → ℝ => fun j => α + c * x j :=
    measurable_pi_iff.2 fun j => by fun_prop
  have hsum : ∀ᵐ x ∂(Q.map fun x j => α + c * x j), ∑ j, x j = n * α + c * s := by
    rw [ae_map_iff hA.aemeasurable (measurableSet_sum_eq _)]
    filter_upwards [hs] with x hx
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx]
    simp
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  rw [Measure.map_map (measurable_pi_apply j) hA]
  have : ((fun f : Fin n → ℝ => f j) ∘ fun (x : Fin n → ℝ) (j : Fin n) => α + c * x j) =
      (fun y : ℝ => α + c * y) ∘ (fun x : Fin n → ℝ => x j) := rfl
  rw [this, ← Measure.map_map (g := fun y : ℝ => α + c * y) (f := fun x : Fin n → ℝ => x j)
    (by fun_prop) (measurable_pi_apply j)]
  exact congrArg (Measure.map _) (hmarg j)

/-- The pushforward of Lebesgue measure under `y ↦ α + c y`, `c ≠ 0`. -/
lemma map_volume_affine {α c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun y => α + c * y) = ENNReal.ofReal |c⁻¹| • volume := by
  have : (fun y : ℝ => α + c * y) = (fun y => α + y) ∘ (fun y => c * y) := rfl
  rw [this, ← Measure.map_map (measurable_const_add α) (measurable_const_mul c),
    Real.map_volume_mul_left hc, Measure.map_smul _ (measurable_const_add α).aemeasurable,
    (measurePreserving_add_left volume α).map_eq]

lemma measurableEmbedding_affine {α c : ℝ} (hc : c ≠ 0) :
    MeasurableEmbedding fun y : ℝ => α + c * y :=
  (Homeomorph.addLeft α).measurableEmbedding.comp
    (Homeomorph.mulLeft₀ c hc).measurableEmbedding

/-- Change of variables `x = α + c y` in a lower Lebesgue integral (no measurability needed). -/
lemma lintegral_affine {α c : ℝ} (hc : c ≠ 0) (G : ℝ → ℝ≥0∞) :
    ∫⁻ y, G (α + c * y) = ENNReal.ofReal |c⁻¹| * ∫⁻ x, G x := by
  rw [← (measurableEmbedding_affine (α := α) hc).lintegral_map, map_volume_affine hc,
    lintegral_smul_measure, smul_eq_mul]

lemma ofReal_abs_inv_mul {c : ℝ} (hc : c ≠ 0) :
    ENNReal.ofReal |c⁻¹| * ENNReal.ofReal |c| = 1 := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel₀ hc, abs_one,
    ENNReal.ofReal_one]

/-- A density on `T` transported by `x = α + c y`: the law of `α + c Y`, where `Y` has density
`|c| g(α + c y)` on the preimage of `T`, has density `g` on `T`. -/
lemma map_withDensity_affine {α c : ℝ} (hc : c ≠ 0) {T : Set ℝ} (hT : MeasurableSet T)
    (g : ℝ → ℝ≥0∞) :
    ((volume.restrict ((fun y => α + c * y) ⁻¹' T)).withDensity
        (fun y => ENNReal.ofReal |c| * g (α + c * y))).map (fun y => α + c * y) =
      (volume.restrict T).withDensity g := by
  have hm : Measurable fun y : ℝ => α + c * y := (measurable_const_mul c).const_add α
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hm hs), Measure.restrict_restrict hs,
    ← lintegral_indicator ((hm hs).inter (hm hT)), ← lintegral_indicator (hs.inter hT)]
  have e : (((fun y => α + c * y) ⁻¹' s ∩ (fun y => α + c * y) ⁻¹' T).indicator
      fun y => ENNReal.ofReal |c| * g (α + c * y)) =
      fun y => (s ∩ T).indicator (fun x => ENNReal.ofReal |c| * g x) (α + c * y) := by
    funext y; simp only [Set.indicator]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  rw [e, lintegral_affine hc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext x
  simp only [Set.indicator]
  split_ifs
  · rw [← mul_assoc, ofReal_abs_inv_mul hc, one_mul]
  · simp

variable {f : ℝ → ℝ} {α β μ : ℝ}

/-- **Corollary 13** (`m:cor:general`), non-increasing case. Let `n ≥ 2`, let `f` be a
non-increasing, right-continuous probability density on `(α, ∞)` vanishing on `[β, ∞)`, with
mean `μ` (written `∫ (x - α) f(x) dx = μ - α`, `μ > α`) satisfying `α + (β - α)/n ≤ μ`, the left
inequality of the mean condition. Then the distribution `F` with density `f` has an
`n`-complete mix with sum `n μ`: the image of the output of Algorithm 11 for the density of
`(X - α)/(μ - α)` under `y ↦ α + (μ - α) y`. -/
theorem cor13_nonincreasing (hn : 2 ≤ n) (hmono : AntitoneOn f (Ioi α))
    (hrc : ∀ x, α < x → ContinuousWithinAt f (Ici x) x) (hβ : ∀ x, β ≤ x → f x = 0)
    (hf1 : ∫⁻ x in Ioi α, ENNReal.ofReal (f x) = 1)
    (hmean : ∫⁻ x in Ioi α, ENNReal.ofReal (x - α) * ENNReal.ofReal (f x) = ENNReal.ofReal (μ - α))
    (hμα : α < μ) (hcond : α + (β - α) / n ≤ μ) :
    ∃ Q : Measure (Fin n → ℝ),
      IsCompleteMix n ((volume.restrict (Ioi α)).withDensity fun x => ENNReal.ofReal (f x)) Q ∧
        ∀ᵐ x ∂Q, ∑ j, x j = n * μ := by
  set c := μ - α with hc_def
  have hc : 0 < c := sub_pos.2 hμα
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set f' : ℝ → ℝ := fun y => c * f (α + c * y) with hf'
  have hpre : (fun y => α + c * y) ⁻¹' Ioi α = Ioi 0 := by
    ext y; simp only [mem_preimage, mem_Ioi]
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  -- the density of `(X - α)/c`
  have hdens : Slabs.densMeas f' = (volume.restrict ((fun y => α + c * y) ⁻¹' Ioi α)).withDensity
      (fun y => ENNReal.ofReal |c| * ENNReal.ofReal (f (α + c * y))) := by
    rw [hpre, Slabs.densMeas]
    congr 1; funext y
    rw [hf', abs_of_pos hc, ENNReal.ofReal_mul hc.le]
  have hmap : (Slabs.densMeas f').map (fun y => α + c * y) =
      (volume.restrict (Ioi α)).withDensity fun x => ENNReal.ofReal (f x) := by
    rw [hdens]
    exact map_withDensity_affine (α := α) (c := c) hc.ne' measurableSet_Ioi
      (fun x => ENNReal.ofReal (f x))
  have hm : Measurable fun y : ℝ => α + c * y := (measurable_const_mul c).const_add α
  -- the hypotheses of Theorem 12 for `f'`
  have hmono' : AntitoneOn f' (Ioi 0) := by
    intro y hy y' hy' hyy'
    simp only [mem_Ioi] at hy hy'
    exact mul_le_mul_of_nonneg_left (hmono (by simp; nlinarith) (by simp; nlinarith)
      (by nlinarith)) hc.le
  have hrc' : ∀ y, 0 < y → ContinuousWithinAt f' (Ici y) y := by
    intro y hy
    have h1 : ContinuousWithinAt (fun y => α + c * y) (Ici y) y :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousWithinAt
    have h2 : ContinuousWithinAt (fun z => f (α + c * z)) (Ici y) y :=
      ContinuousWithinAt.comp (g := f) (f := fun z => α + c * z) (t := Ici (α + c * y))
        (hrc (α + c * y) (by nlinarith)) h1 (fun z hz => by
          simp only [mem_Ici] at hz ⊢; nlinarith)
    exact continuousWithinAt_const.mul h2
  have hB' : ∀ y, (β - α) / c ≤ y → f' y = 0 := by
    intro y hy
    have : β ≤ α + c * y := by
      have := (div_le_iff₀ hc).1 hy; linarith
    simp [hf', hβ _ this]
  have hBn : (β - α) / c ≤ n := by
    rw [div_le_iff₀ hc]
    have := (div_le_iff₀ hn0).1 (show (β - α) / n ≤ c by linarith)
    linarith
  have hf1' : ∫⁻ y in Ioi 0, ENNReal.ofReal (f' y) = 1 := by
    have h := congrArg (fun m : Measure ℝ => m univ) hmap
    simp only [Measure.map_apply hm MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Slabs.densMeas] at h
    rw [h, hf1]
  have hmean1 : ∫⁻ y in Ioi 0, ENNReal.ofReal y * ENNReal.ofReal (f' y) = 1 := by
    rw [← lintegral_indicator measurableSet_Ioi]
    have e : (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal y * ENNReal.ofReal (f' y)) =
        fun y => (Ioi α).indicator (fun x => ENNReal.ofReal (x - α) * ENNReal.ofReal (f x))
          (α + c * y) := by
      funext y
      simp only [Set.indicator, mem_Ioi]
      by_cases hy : 0 < y
      · have hy' : α < α + c * y := by nlinarith
        simp only [hy, hy', ite_true, hf']
        rw [← ENNReal.ofReal_mul hy.le, ← ENNReal.ofReal_mul (by nlinarith)]
        congr 1; ring
      · have hy' : ¬ α < α + c * y := by nlinarith
        simp only [hy, hy', ite_false]
    rw [e, lintegral_affine hc.ne', lintegral_indicator measurableSet_Ioi, hmean,
      abs_of_pos (inv_pos.2 hc), ← ENNReal.ofReal_mul (inv_pos.2 hc).le, inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one]
  obtain ⟨Q', hQ', hsum'⟩ := mono_completelyMixable hn hmono' hrc' hBn hB' hf1' hmean1
  obtain ⟨hQ, hsum⟩ := isCompleteMix_affine hQ' hsum' α c
  refine ⟨_, hmap ▸ hQ, hsum.mono fun x hx => ?_⟩
  rw [hx, hc_def]; ring

/-- **Corollary 13** (`m:cor:general`), non-decreasing case. Let `n ≥ 2`, let `f` be a
non-decreasing, left-continuous probability density on `(-∞, β)` vanishing on `(-∞, α]`, with
mean `μ` (written `∫ (β - x) f(x) dx = β - μ`, `μ < β`) satisfying `μ ≤ β - (β - α)/n`, the
right inequality of the mean condition. Then the distribution with density `f` has an
`n`-complete mix with sum `n μ`: the reflection `x ↦ α + β - x` of the complete mix of the
non-increasing case for the law of `α + β - X`. -/
theorem cor13_nondecreasing (hn : 2 ≤ n) (hmono : MonotoneOn f (Iio β))
    (hlc : ∀ x, x < β → ContinuousWithinAt f (Iic x) x) (hα : ∀ x, x ≤ α → f x = 0)
    (hf1 : ∫⁻ x in Iio β, ENNReal.ofReal (f x) = 1)
    (hmean : ∫⁻ x in Iio β, ENNReal.ofReal (β - x) * ENNReal.ofReal (f x) = ENNReal.ofReal (β - μ))
    (hμβ : μ < β) (hcond : μ ≤ β - (β - α) / n) :
    ∃ Q : Measure (Fin n → ℝ),
      IsCompleteMix n ((volume.restrict (Iio β)).withDensity fun x => ENNReal.ofReal (f x)) Q ∧
        ∀ᵐ x ∂Q, ∑ j, x j = n * μ := by
  set g : ℝ → ℝ := fun x => f (α + β + (-1) * x) with hg
  have hpre : (fun y => α + β + (-1) * y) ⁻¹' Iio β = Ioi α := by
    ext y; simp only [mem_preimage, mem_Iio, mem_Ioi]; constructor <;> intro h <;> linarith
  have hmap : ((volume.restrict (Ioi α)).withDensity fun x => ENNReal.ofReal (g x)).map
      (fun y => α + β + (-1) * y) =
      (volume.restrict (Iio β)).withDensity fun x => ENNReal.ofReal (f x) := by
    rw [← map_withDensity_affine (by norm_num : (-1 : ℝ) ≠ 0) measurableSet_Iio, hpre]
    congr 2; funext y; simp [hg]
  have hmono' : AntitoneOn g (Ioi α) := by
    intro y hy y' hy' hyy'
    simp only [mem_Ioi] at hy hy'
    exact hmono (by simp; linarith) (by simp; linarith) (by linarith)
  have hrc' : ∀ y, α < y → ContinuousWithinAt g (Ici y) y := by
    intro y hy
    have h1 : ContinuousWithinAt (fun y => α + β + (-1) * y) (Ici y) y :=
      (continuous_const.add (continuous_const.mul continuous_id)).continuousWithinAt
    exact ContinuousWithinAt.comp (g := f) (f := fun z => α + β + (-1) * z)
      (t := Iic (α + β + (-1) * y)) (hlc (α + β + (-1) * y) (by linarith)) h1 (fun z hz => by
        simp only [mem_Ici, mem_Iic] at hz ⊢; linarith)
  have hβ' : ∀ y, β ≤ y → g y = 0 := fun y hy => hα _ (by linarith)
  have hcv : ∀ G : ℝ → ℝ≥0∞, ∫⁻ y, G (α + β + (-1) * y) = ∫⁻ x, G x := fun G => by
    rw [lintegral_affine (by norm_num : (-1 : ℝ) ≠ 0)]; simp
  have hf1' : ∫⁻ x in Ioi α, ENNReal.ofReal (g x) = 1 := by
    rw [← lintegral_indicator measurableSet_Ioi, ← hf1, ← lintegral_indicator measurableSet_Iio,
      ← hcv]
    congr 1; funext y
    simp only [Set.indicator, mem_Ioi, mem_Iio, hg]
    rw [show α + β + -1 * (α + β + -1 * y) = y by ring]
    split_ifs <;> first | rfl | (exfalso; linarith)
  have hmean' : ∫⁻ x in Ioi α, ENNReal.ofReal (x - α) * ENNReal.ofReal (g x) =
      ENNReal.ofReal ((α + β - μ) - α) := by
    rw [show (α + β - μ) - α = β - μ by ring, ← hmean, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Iio, ← hcv]
    congr 1; funext y
    simp only [Set.indicator, mem_Ioi, mem_Iio, hg]
    rw [show α + β + -1 * (α + β + -1 * y) = y by ring,
      show α + β + -1 * y - α = β - y by ring]
    split_ifs <;> first | rfl | (exfalso; linarith)
  obtain ⟨Q', hQ', hsum'⟩ := cor13_nonincreasing (μ := α + β - μ) hn hmono' hrc' hβ' hf1' hmean'
    (by linarith) (by linarith)
  obtain ⟨hQ, hsum⟩ := isCompleteMix_affine hQ' hsum' (α + β) (-1)
  refine ⟨_, hmap ▸ hQ, hsum.mono fun x hx => ?_⟩
  rw [hx]; ring

end Cor13

end SlabsMix

end Mixes
