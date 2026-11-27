import Mixes.Uniform
import Mixes.JointSplit
import Mixes.Pieces

set_option linter.deprecated false

/-!
# Tilts with two steps and prescribed sums of uniform random variables

Section `as:sec:asym` of draft 14: Lemma `as:lem:tilt` and Proposition `as:prop:window`.

## Statements (stable; other files use them in exactly this form)

* `InAgg F ν`: `ν ∈ 𝒜_n(F₁, …, Fₙ)`, the aggregation set: there is a probability measure on
  `n`-tuples with marginals `F j` under which the sum `x₁ + ⋯ + xₙ` has law `ν`.
* `box c H = c + ∏ᵢ [-Hᵢ, Hᵢ] ⊆ Fin d → ℝ`, and `unifSet (box c H)` is `U(Q)`.
* `tilt H γ`: the distribution `P_{H,γ}` with density `(1-γ)/(2H)` on `(-H,0)` and
  `(1+γ)/(2H)` on `(0,H)`.
* `PropWindow`: Proposition `as:prop:window` for `d`-dimensional boxes and `mᵢ ≥ 4`;
  `PropWindowThree`: its last sentence (`d = 1`, `m = 3`), stated on `ℝ`;
  `PropWindowReal`: the case `d = 1` stated on `ℝ` (with `unifI`), for convenience.

## Main theorems

* `lemTilt : LemTilt` (Lemma `as:lem:tilt`); with a measurable family: `tiltKH m H γ` is a
  measurable (`measurable_tiltKH`) kernel of probability measures (`isProb_tiltKH`), and for
  `TiltRange m γ` an `m`-complete mix of `P_{H,γ}` with sum `m γ H / 2` (`tiltKH_spec`).
* `eq_affine`: the identity `as:eq:affine`, `∫ P_{H,γ} ρ(dγ) = P_{H,γ̄}`.
* `propWindow : PropWindow`, `propWindowReal : PropWindowReal`,
  `propWindowThree : PropWindowThree` (Proposition `as:prop:window`). The tuples are explicit:
  `ν.bind (boxK c H mi)` (`window_box`), resp. `ν.bind (winK m c H)` (`window_one`), i.e. the
  conditional law of the tuple given the sum `t` is a fixed kernel of `t`, built from the
  Archimedes measure `archPlane` and finitely many uniform choices.

## Differences from the paper

* The complete mix of `P_{1,-p}` (`p ≥ 0`) is not taken from Theorem `m:thm:two`, but from two
  explicit mixtures of admissible tuples (Lemma 3 with Lemma 1): for `m ≥ 4` the tuples
  `(a·[-1,0], b·[0,1], c·[-1,1], [-1,α-1])` and `((a+1)·[-1,0], b·[0,1], (c-1)·[-1,1], [α-1,0])`
  with weights `α`, `1-α` (`fl`, `fr`, `fw`, `f_marg`); for `m = 3` (`p ≤ 2/3`) the tuples
  `[-p,0]³`, `([-1,-p],[-p,1],[-1,1-p])`, `([-1,-p],[-1,-p],[1-p,1])` with weights `p²`,
  `(1-p²)(1-p/2)`, `(1-p²)p/2` (`gl`, `gr`, `gw`, `g_marg`). The second family is what
  Theorem `m:thm:two` (ii) with case (A) gives for `n = 3`, `a = 2/(2-p)`, `b = 2a`.
  The joint mixes of Lemma 1 are chosen measurably in the parameter (`jmVec`, `jmK`): the
  partition `{k} ∪ G ∪ H` is the first good one in a fixed list.
* For `γ > 0` the complete mix is the reflection of the one for `-γ`.
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Mixes

namespace AsymWindow

open Classical

/-! ### Definitions -/

/-- `ν ∈ 𝒜_n(F 0, …, F (n-1))`: there are random variables `X j ∼ F j` with
`X 0 + ⋯ + X (n-1) ∼ ν`, i.e. a probability measure `P` on `n`-tuples with marginals `F j`
under which the sum has law `ν`. -/
def InAgg {E : Type*} [MeasurableSpace E] [AddCommMonoid E] {n : ℕ} (F : Fin n → Measure E)
    (ν : Measure E) : Prop :=
  ∃ P : Measure (Fin n → E), IsProbabilityMeasure P ∧ (∀ j, P.map (fun x => x j) = F j) ∧
    P.map (fun x => ∑ j, x j) = ν

/-- The box `Q = c + ∏ᵢ [-Hᵢ, Hᵢ]` in `ℝ^d = Fin d → ℝ`. -/
def box {d : ℕ} (c H : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Icc (c i - H i) (c i + H i)

/-- The density of `P_{H,γ}`: `(1-γ)/(2H)` on `(-H,0)`, `(1+γ)/(2H)` on `(0,H)`, `0` elsewhere. -/
def tiltDens (H γ x : ℝ) : ℝ :=
  if -H < x ∧ x < 0 then (1 - γ) / (2 * H) else if 0 < x ∧ x < H then (1 + γ) / (2 * H) else 0

/-- `P_{H,γ}`, the distribution with density `tiltDens H γ` (a probability measure for `H > 0`
and `|γ| ≤ 1`). -/
def tilt (H γ : ℝ) : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (tiltDens H γ x)

/-- The parameter range of Lemma `as:lem:tilt`: `m ≥ 4` and `|γ| ≤ 1`, or `m = 3` and
`|γ| ≤ 2/3`. -/
def TiltRange (m : ℕ) (γ : ℝ) : Prop := (4 ≤ m ∧ |γ| ≤ 1) ∨ (m = 3 ∧ |γ| ≤ 2 / 3)

/-! ### The statements -/

/-- **Lemma `as:lem:tilt`** (statement). In the range `TiltRange m γ`, `P_{H,γ}` is
`m`-completely mixable by a complete mix with sum `m γ H / 2`. -/
def LemTilt : Prop :=
  ∀ (m : ℕ) (H γ : ℝ), 0 < H → TiltRange m γ →
    ∃ P : Measure (Fin m → ℝ), IsCompleteMix m (tilt H γ) P ∧
      ∀ᵐ x ∂P, ∑ j, x j = m * γ * H / 2

/-- **Proposition `as:prop:window`** (statement, `mᵢ ≥ 4`). Let `Q = c + ∏ᵢ [-Hᵢ, Hᵢ]` with
`Hᵢ > 0`, `m = m₁ + ⋯ + m_d` with `mᵢ ≥ 4`, and let `ν` be a probability measure on `ℝ^d` with
mean `m c` that is carried by `m c + ∏ᵢ [-mᵢHᵢ/2, mᵢHᵢ/2]`. Then `ν ∈ 𝒜_m(U(Q))`. -/
def PropWindow : Prop :=
  ∀ (d : ℕ) (c H : Fin d → ℝ) (mi : Fin d → ℕ) (ν : Measure (Fin d → ℝ)),
    (∀ i, 0 < H i) → (∀ i, 4 ≤ mi i) → IsProbabilityMeasure ν →
    (∀ᵐ x ∂ν, ∀ i, |x i - (∑ k, mi k : ℕ) * c i| ≤ mi i * H i / 2) →
    ∫ x, x ∂ν = ((∑ k, mi k : ℕ) : ℝ) • c →
    InAgg (fun _ : Fin (∑ k, mi k) => unifSet (box c H)) ν

/-- **Proposition `as:prop:window`, `d = 1`** (on `ℝ`, `m ≥ 4`): a probability measure with mean
`m c` carried by `[m c - m H/2, m c + m H/2]` belongs to `𝒜_m(U[c-H, c+H])`. -/
def PropWindowReal : Prop :=
  ∀ (m : ℕ) (c H : ℝ) (ν : Measure ℝ), 0 < H → 4 ≤ m → IsProbabilityMeasure ν →
    (∀ᵐ x ∂ν, |x - m * c| ≤ m * H / 2) → ∫ x, x ∂ν = m * c →
    InAgg (fun _ : Fin m => unifI (c - H) (c + H)) ν

/-- **Proposition `as:prop:window`, last sentence** (`d = 1`, `m = 3`, on `ℝ`): a probability
measure with mean `3 c` carried by `[3c - H, 3c + H]` belongs to `𝒜_3(U[c-H, c+H])`. -/
def PropWindowThree : Prop :=
  ∀ (c H : ℝ) (ν : Measure ℝ), 0 < H → IsProbabilityMeasure ν →
    (∀ᵐ x ∂ν, |x - 3 * c| ≤ H) → ∫ x, x ∂ν = 3 * c →
    InAgg (fun _ : Fin 3 => unifI (c - H) (c + H)) ν

/-! ## Proofs -/


/-! ### Uniform distributions: splitting, and real values -/

instance (l r : ℝ) : IsProbabilityMeasure (unifI l r) := unifI_isProb l r

/-- `U[l,r] = ((c-l)/(r-l)) U[l,c] + ((r-c)/(r-l)) U[c,r]` for `l ≤ c ≤ r`, `l < r`. -/
lemma unifI_split' {l c r : ℝ} (hlc : l ≤ c) (hcr : c ≤ r) (hlr : l < r) :
    unifI l r = ENNReal.ofReal ((c - l) / (r - l)) • unifI l c +
      ENNReal.ofReal ((r - c) / (r - l)) • unifI c r := by
  have h := congrArg (Measure.map (fun t => l + t))
    (unifI_split (sub_pos.2 hlr) (sub_nonneg.2 hlc) (by linarith : c - l ≤ r - l))
  rw [Measure.map_add _ _ (measurable_const_add l), Measure.map_smul, Measure.map_smul,
    map_unifI_const_add, map_unifI_const_add, map_unifI_const_add] at h
  all_goals try exact (measurable_const_add l).aemeasurable
  simp only [add_zero, add_sub_cancel] at h
  rw [h]
  congr 3
  field_simp
  ring

/-- The real value of `U[l,r]` on a set. -/
def uv (A : Set ℝ) (l r : ℝ) : ℝ := (unifI l r A).toReal

lemma uv_split (A : Set ℝ) {l c r : ℝ} (hlc : l ≤ c) (hcr : c ≤ r) (hlr : l < r) :
    uv A l r = (c - l) / (r - l) * uv A l c + (r - c) / (r - l) * uv A c r := by
  have hd : 0 < r - l := sub_pos.2 hlr
  unfold uv
  rw [unifI_split' hlc hcr hlr, add_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (by linarith) hd.le),
    ENNReal.toReal_ofReal (div_nonneg (by linarith) hd.le)]

/-! ### Tilts as mixtures of two uniform distributions -/

lemma tilt_eq {H γ : ℝ} (hH : 0 < H) (hγ : |γ| ≤ 1) :
    tilt H γ = ENNReal.ofReal ((1 - γ) / 2) • unifI (-H) 0 +
      ENNReal.ofReal ((1 + γ) / 2) • unifI 0 H := by
  obtain ⟨hγ1, hγ2⟩ := abs_le.1 hγ
  have hf : (fun x => ENNReal.ofReal (tiltDens H γ x)) =
      (Set.Ioo (-H) 0).indicator (fun _ => ENNReal.ofReal ((1 - γ) / (2 * H))) +
      (Set.Ioo 0 H).indicator (fun _ => ENNReal.ofReal ((1 + γ) / (2 * H))) := by
    funext x
    simp only [tiltDens, Pi.add_apply, Set.indicator, Set.mem_Ioo]
    split_ifs <;> first | simp | (exfalso; linarith)
  rw [tilt, hf, withDensity_add_left ((measurable_const.indicator measurableSet_Ioo)),
    withDensity_indicator measurableSet_Ioo, withDensity_indicator measurableSet_Ioo,
    withDensity_const, withDensity_const, Measure.restrict_congr_set Ioo_ae_eq_Icc,
    Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := H)),
    unifI_of_lt (by linarith : -H < 0), unifI_of_lt hH, smul_smul, smul_smul]
  congr 2
  · rw [show (1 - γ) / (2 * H) = (1 - γ) / 2 / (0 - -H) by ring,
      ENNReal.ofReal_div_of_pos (by linarith), div_eq_mul_inv]
  · rw [show (1 + γ) / (2 * H) = (1 + γ) / 2 / (H - 0) by ring,
      ENNReal.ofReal_div_of_pos (by linarith), div_eq_mul_inv]

lemma isProb_tilt {H γ : ℝ} (hH : 0 < H) (hγ : |γ| ≤ 1) : IsProbabilityMeasure (tilt H γ) := by
  obtain ⟨hγ1, hγ2⟩ := abs_le.1 hγ
  constructor
  rw [tilt_eq hH hγ, add_apply, smul_apply, smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add (by linarith) (by linarith),
    show (1 - γ) / 2 + (1 + γ) / 2 = 1 by ring, ENNReal.ofReal_one]

/-! ### Sums over tuples of three kinds of intervals and a last one -/

/-- Left ends: `A` copies of `[-1,0]`, then `B` copies of `[0,1]`, then copies of `[-1,1]` up to
index `N - 1`, then `[L, R]` at index `N`. -/
def kl (N A B : ℕ) (L : ℝ) (j : ℕ) : ℝ :=
  if j < A then -1 else if j < A + B then 0 else if j < N then -1 else L
/-- Right ends. -/
def kr (N A B : ℕ) (R : ℝ) (j : ℕ) : ℝ :=
  if j < A then 0 else if j < A + B then 1 else if j < N then 1 else R

lemma sum_kind {M : Type*} [AddCommMonoid M] (N A B C : ℕ) (h : A + B + C = N) (L R : ℝ)
    (f : ℝ → ℝ → M) :
    ∑ j : Fin (N + 1), f (kl N A B L j) (kr N A B R j) =
      A • f (-1) 0 + B • f 0 1 + C • f (-1) 1 + f L R := by
  rw [Fin.sum_univ_castSucc]
  have hlast : f (kl N A B L (Fin.last N : ℕ)) (kr N A B R (Fin.last N : ℕ)) = f L R := by
    simp only [Fin.val_last, kl, kr]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
  rw [hlast]
  congr 1
  simp only [Fin.coe_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (kl N A B L j) (kr N A B R j)) N,
    ← Finset.sum_range_add_sum_Ico _ (by omega : A ≤ N),
    ← Finset.sum_Ico_consecutive _ (by omega : A ≤ A + B) (by omega : A + B ≤ N)]
  have e1 : ∑ j ∈ Finset.range A, f (kl N A B L j) (kr N A B R j) = A • f (-1) 0 := by
    rw [Finset.sum_congr rfl (g := fun _ => f (-1) 0), Finset.sum_const, Finset.card_range]
    intro j hj; rw [Finset.mem_range] at hj; simp [kl, kr, hj]
  have e2 : ∑ j ∈ Finset.Ico A (A + B), f (kl N A B L j) (kr N A B R j) = B • f 0 1 := by
    rw [Finset.sum_congr rfl (g := fun _ => f 0 1), Finset.sum_const, Nat.card_Ico,
      Nat.add_sub_cancel_left]
    intro j hj; rw [Finset.mem_Ico] at hj
    simp only [kl, kr]; rw [if_neg (by omega), if_pos hj.2, if_neg (by omega), if_pos hj.2]
  have e3 : ∑ j ∈ Finset.Ico (A + B) N, f (kl N A B L j) (kr N A B R j) = C • f (-1) 1 := by
    rw [Finset.sum_congr rfl (g := fun _ => f (-1) 1), Finset.sum_const, Nat.card_Ico,
      show N - (A + B) = C by omega]
    intro j hj; rw [Finset.mem_Ico] at hj
    simp only [kl, kr]
    rw [if_neg (by omega), if_neg (by omega), if_pos hj.2, if_neg (by omega), if_neg (by omega),
      if_pos hj.2]
  rw [e1, e2, e3, add_assoc]

lemma kind_le (N A B : ℕ) {L R : ℝ} (h : L ≤ R) (j : ℕ) : kl N A B L j ≤ kr N A B R j := by
  unfold kl kr; split_ifs <;> linarith

lemma kind_len_le (N A B : ℕ) {L R : ℝ} (h : R - L ≤ 2) (j : ℕ) :
    kr N A B R j - kl N A B L j ≤ 2 := by
  unfold kl kr; split_ifs <;> linarith

lemma kind_len_le_one (N A B : ℕ) (hN : A + B = N) {L R : ℝ} (h : R - L ≤ 1) (j : ℕ) :
    kr N A B R j - kl N A B L j ≤ 1 := by
  unfold kl kr; split_ifs <;> linarith

/-! ### Real values of mixtures -/

lemma mixMarg_apply {ι : Type*} [Fintype ι] {n : ℕ} (hn : n ≠ 0) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (μ : ι → Fin n → Measure ℝ) [∀ i j, IsFiniteMeasure (μ i j)]
    (A : Set ℝ) :
    (∑ i, ENNReal.ofReal (w i) • ((n : ℝ≥0∞)⁻¹ • ∑ j, μ i j)) A =
      ENNReal.ofReal (∑ i, w i * ((n : ℝ)⁻¹ * ∑ j, (μ i j A).toReal)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hw i)
    (mul_nonneg (inv_nonneg.2 hn'.le) (Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg))]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul (hw i), ENNReal.ofReal_mul (inv_nonneg.2 hn'.le),
    ENNReal.ofReal_sum_of_nonneg fun j _ => ENNReal.toReal_nonneg, ENNReal.ofReal_inv_of_pos hn',
    ENNReal.ofReal_natCast]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma tilt_apply {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set ℝ) :
    tilt 1 (-p) A = ENNReal.ofReal ((1 + p) / 2 * uv A (-1) 0 + (1 - p) / 2 * uv A 0 1) := by
  rw [tilt_eq one_pos (by rw [abs_neg, abs_of_nonneg hp0]; exact hp1), add_apply, smul_apply,
    smul_apply, smul_eq_mul, smul_eq_mul, sub_neg_eq_add, ← sub_eq_add_neg, uv, uv,
    ENNReal.ofReal_add (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
      (mul_nonneg (by linarith) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-! ### The family for `m = N + 1 ≥ 4` -/

/-- `K = m (1 - p)`. -/
def fK (N : ℕ) (p : ℝ) : ℝ := (N + 1) * (1 - p)
/-- Case II: `K > N`. -/
def fII (N : ℕ) (p : ℝ) : Prop := (N : ℝ) < fK N p
/-- The number of copies of `[-1,1]` in the first tuple. -/
def fc (N : ℕ) (p : ℝ) : ℕ := if fII N p then N - 1 else min (⌊fK N p⌋₊ + 1) N
/-- The number of copies of `[0,1]`. -/
def fb (N : ℕ) (p : ℝ) : ℕ := if fII N p then 1 else 0
/-- The number of copies of `[-1,0]` in the first tuple. -/
def fa (N : ℕ) (p : ℝ) : ℕ := N - fb N p - fc N p
/-- The weight of the first tuple. -/
def fα (N : ℕ) (p : ℝ) : ℝ := if fII N p then fK N p - N else fK N p - fc N p + 1

lemma f_valid {N : ℕ} (hN : 3 ≤ N) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 ≤ fc N p ∧ fb N p + fc N p ≤ N ∧ 0 ≤ fα N p ∧ fα N p ≤ 1 ∧
      fK N p = fα N p + fc N p + 2 * fb N p - 1 := by
  have hK0 : 0 ≤ fK N p := mul_nonneg (by positivity) (by linarith)
  have hKN : fK N p ≤ N + 1 := by unfold fK; nlinarith
  by_cases h : fII N p
  · have hN1 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [fc, fb, fα, h, if_true]
    unfold fII at h
    refine ⟨by omega, by omega, by linarith, by linarith, ?_⟩
    rw [hN1]; push_cast; ring
  · simp only [fc, fb, fα, h, if_false]
    unfold fII at h; push Not at h
    have hfl := Nat.floor_le hK0
    have hfl2 := Nat.lt_floor_add_one (fK N p)
    rcases le_total (⌊fK N p⌋₊ + 1) N with h1 | h1
    · rw [min_eq_left h1]
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩ <;> push_cast <;> linarith
    · rw [min_eq_right h1]
      have : (N : ℝ) ≤ ⌊fK N p⌋₊ + 1 := by exact_mod_cast h1
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-- Endpoints of the two tuples: `τ' = (a·[-1,0], b·[0,1], c·[-1,1], [-1, α-1])` with weight `α`
and `τ'' = ((a+1)·[-1,0], b·[0,1], (c-1)·[-1,1], [α-1, 0])` with weight `1 - α`. -/
def fl (m : ℕ) (i : Fin 2) (p : ℝ) (j : Fin m) : ℝ :=
  if i = 0 then kl (m - 1) (fa (m - 1) p) (fb (m - 1) p) (-1) j
  else kl (m - 1) (fa (m - 1) p + 1) (fb (m - 1) p) (fα (m - 1) p - 1) j
def fr (m : ℕ) (i : Fin 2) (p : ℝ) (j : Fin m) : ℝ :=
  if i = 0 then kr (m - 1) (fa (m - 1) p) (fb (m - 1) p) (fα (m - 1) p - 1) j
  else kr (m - 1) (fa (m - 1) p + 1) (fb (m - 1) p) 0 j
def fw (N : ℕ) (i : Fin 2) (p : ℝ) : ℝ := if i = 0 then fα N p else 1 - fα N p

/-- The algebra of the marginal identity for the family. -/
lemma f_alg {N a b c α p X Z W U1 U2 : ℝ} (hN : 0 < N + 1) (habc : a + b + c = N)
    (hK : (N + 1) * (1 - p) = α + c + 2 * b - 1) (hX : X = α * U1 + (1 - α) * U2)
    (hW : W = 1 / 2 * X + 1 / 2 * Z) :
    α * ((N + 1)⁻¹ * (a * X + b * Z + c * W + U1)) +
      (1 - α) * ((N + 1)⁻¹ * ((a + 1) * X + b * Z + (c - 1) * W + U2)) =
      (1 + p) / 2 * X + (1 - p) / 2 * Z := by
  have hp : p = 1 - (α + c + 2 * b - 1) / (N + 1) := by field_simp; linarith
  subst hp
  have ha : a = N - b - c := by linarith
  subst ha hX hW
  field_simp
  ring

lemma fw_nonneg {N : ℕ} (hN : 3 ≤ N) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin 2) :
    0 ≤ fw N i p := by
  obtain ⟨-, -, h1, h2, -⟩ := f_valid hN hp0 hp1
  unfold fw; split_ifs <;> linarith

theorem f_marg {N : ℕ} (hN : 3 ≤ N) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ i, ENNReal.ofReal (fw N i p) •
        (((N + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j, unifI (fl (N + 1) i p j) (fr (N + 1) i p j)) =
      tilt 1 (-p) := by
  obtain ⟨hc1, hbc, hα0, hα1, hK⟩ := f_valid hN hp0 hp1
  ext A hA
  rw [mixMarg_apply (by omega) _ (fw_nonneg hN hp0 hp1), tilt_apply hp0 hp1]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [fw, fl, fr, Fin.isValue, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false,
    Nat.add_sub_cancel]
  have habc : fa N p + fb N p + fc N p = N := by unfold fa; omega
  rw [sum_kind N (fa N p) (fb N p) (fc N p) habc (-1) (fα N p - 1)
      (fun l r => (unifI l r A).toReal),
    sum_kind N (fa N p + 1) (fb N p) (fc N p - 1) (by omega) (fα N p - 1) 0
      (fun l r => (unifI l r A).toReal)]
  simp only [nsmul_eq_mul]
  have hW := uv_split A (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (-1 : ℝ) < 1)
  have hX := uv_split A (by linarith : (-1 : ℝ) ≤ fα N p - 1) (by linarith : fα N p - 1 ≤ 0)
    (by norm_num : (-1 : ℝ) < 0)
  norm_num at hW hX
  simp only [uv] at hW hX
  have hc' : ((fc N p - 1 : ℕ) : ℝ) = fc N p - 1 := by rw [Nat.cast_sub hc1]; simp
  have habc' : (fa N p : ℝ) + fb N p + fc N p = N := by exact_mod_cast habc
  rw [hc', Nat.cast_add, Nat.cast_one]
  push_cast
  refine f_alg (by positivity) habc' (by rw [← hK]; rfl) ?_ hW
  rw [hX]

theorem f_tuples {N : ℕ} (hN : 3 ≤ N) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin 2) :
    (∀ j, fl (N + 1) i p j ≤ fr (N + 1) i p j) ∧
    (∀ j, 2 * (fr (N + 1) i p j - fl (N + 1) i p j) ≤
      ∑ j', (fr (N + 1) i p j' - fl (N + 1) i p j')) ∧
    ∑ j, (fl (N + 1) i p j + fr (N + 1) i p j) = 2 * (((N + 1 : ℕ) : ℝ) * (-p) / 2) := by
  obtain ⟨hc1, hbc, hα0, hα1, hK⟩ := f_valid hN hp0 hp1
  have habc : fa N p + fb N p + fc N p = N := by unfold fa; omega
  have habc' : (fa N p : ℝ) + fb N p + fc N p = N := by exact_mod_cast habc
  have hc' : ((fc N p - 1 : ℕ) : ℝ) = fc N p - 1 := by rw [Nat.cast_sub hc1]; simp
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hc1' : (1 : ℝ) ≤ fc N p := by exact_mod_cast hc1
  unfold fK at hK
  fin_cases i
  · simp only [fl, fr, Fin.zero_eta, Fin.isValue, if_true, Nat.add_sub_cancel]
    refine ⟨fun j => kind_le _ _ _ (by linarith) _, fun j => ?_, ?_⟩
    · rw [sum_kind N _ _ _ habc (-1) (fα N p - 1) (fun l r => r - l)]
      have := kind_len_le N (fa N p) (fb N p) (L := -1) (R := fα N p - 1) (by linarith) j
      simp only [nsmul_eq_mul]; nlinarith
    · rw [sum_kind N _ _ _ habc (-1) (fα N p - 1) (fun l r => l + r)]
      simp only [nsmul_eq_mul]; push_cast; nlinarith
  · simp only [fl, fr, Fin.mk_one, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, if_false,
      Nat.add_sub_cancel]
    have habc2 : fa N p + 1 + fb N p + (fc N p - 1) = N := by omega
    refine ⟨fun j => kind_le _ _ _ (by linarith) _, fun j => ?_, ?_⟩
    · rw [sum_kind N _ _ _ habc2 (fα N p - 1) 0 (fun l r => r - l)]
      simp only [nsmul_eq_mul]; rw [hc']; push_cast
      rcases Nat.lt_or_ge 1 (fc N p) with h2 | h2
      · have := kind_len_le N (fa N p + 1) (fb N p) (L := fα N p - 1) (R := 0) (by linarith) j
        have : (2 : ℝ) ≤ fc N p := by exact_mod_cast h2
        nlinarith
      · have := kind_len_le_one N (fa N p + 1) (fb N p) (by omega) (L := fα N p - 1) (R := 0)
          (by linarith) j
        have : (fc N p : ℝ) = 1 := by exact_mod_cast le_antisymm h2 hc1
        nlinarith
    · rw [sum_kind N _ _ _ habc2 (fα N p - 1) 0 (fun l r => l + r)]
      simp only [nsmul_eq_mul]; rw [hc']; push_cast; nlinarith

/-! ### The family for `m = 3` -/

/-- Left ends of the three tuples `([-p,0]³)`, `([-1,-p], [-p,1], [-1,1-p])`,
`([-1,-p], [-1,-p], [1-p,1])` (only `j < 3` matters). -/
def gl (m : ℕ) (i : Fin 3) (p : ℝ) (j : Fin m) : ℝ :=
  if i = 0 then -p
  else if i = 1 then (if (j : ℕ) = 1 then -p else -1)
  else (if (j : ℕ) = 2 then 1 - p else -1)
/-- Right ends. -/
def gr (m : ℕ) (i : Fin 3) (p : ℝ) (j : Fin m) : ℝ :=
  if i = 0 then 0
  else if i = 1 then (if (j : ℕ) = 0 then -p else if (j : ℕ) = 1 then 1 else 1 - p)
  else (if (j : ℕ) = 2 then 1 else -p)
/-- Weights `p²`, `(1-p²)(1-p/2)`, `(1-p²) p/2`. -/
def gw (i : Fin 3) (p : ℝ) : ℝ :=
  if i = 0 then p ^ 2 else if i = 1 then (1 - p ^ 2) * (1 - p / 2) else (1 - p ^ 2) * (p / 2)

lemma gw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin 3) : 0 ≤ gw i p := by
  have : 0 ≤ 1 - p ^ 2 := by nlinarith
  unfold gw; split_ifs
  · positivity
  · exact mul_nonneg this (by linarith)
  · exact mul_nonneg this (by linarith)

lemma g_alg {p Q Y Rr S1 S2 X Z W : ℝ} (hp0 : 0 ≤ p)
    (hs1 : W = (2 - p) / 2 * S1 + p / 2 * S2) (hs2 : W = 1 / 2 * X + 1 / 2 * Z)
    (hs3 : X = (1 - p) * Q + p * Y) (hs4 : Rr = p / (1 + p) * Y + 1 / (1 + p) * Z) :
    p ^ 2 * ((3 : ℝ)⁻¹ * (Y + Y + Y)) + (1 - p ^ 2) * (1 - p / 2) * ((3 : ℝ)⁻¹ * (Q + Rr + S1)) +
      (1 - p ^ 2) * (p / 2) * ((3 : ℝ)⁻¹ * (Q + Q + S2)) =
      (1 + p) / 2 * X + (1 - p) / 2 * Z := by
  have h1 : (1 + p) ≠ 0 := by linarith
  linear_combination (norm := skip) (-(1 - p ^ 2) / 3) * hs1 + ((1 - p ^ 2) / 3) * hs2 +
    ((1 - p ^ 2) / 6 - (1 + p) / 2) * hs3 + ((1 - p ^ 2) * (1 - p / 2) / 3) * hs4
  field_simp
  ring

theorem g_marg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2 / 3) :
    ∑ i, ENNReal.ofReal (gw i p) •
        (((3 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j, unifI (gl 3 i p j) (gr 3 i p j)) = tilt 1 (-p) := by
  ext A hA
  rw [mixMarg_apply (by norm_num) _ (gw_nonneg hp0 (by linarith)), tilt_apply hp0 (by linarith)]
  congr 1
  simp only [Fin.sum_univ_three, gw, gl, gr, Fin.isValue, if_true,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  have hs1 := uv_split A (by linarith : (-1 : ℝ) ≤ 1 - p) (by linarith : 1 - p ≤ 1)
    (by norm_num : (-1 : ℝ) < 1)
  have hs2 := uv_split A (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (-1 : ℝ) < 1)
  have hs3 := uv_split A (by linarith : (-1 : ℝ) ≤ -p) (by linarith : -p ≤ 0)
    (by norm_num : (-1 : ℝ) < 0)
  have hs4 := uv_split A (by linarith : -p ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : -p < 1)
  simp only [uv] at hs1 hs2 hs3 hs4
  have e := g_alg (p := p) (Q := (unifI (-1) (-p) A).toReal) (Y := (unifI (-p) 0 A).toReal)
    (Rr := (unifI (-p) 1 A).toReal) (S1 := (unifI (-1) (1 - p) A).toReal)
    (S2 := (unifI (1 - p) 1 A).toReal) (X := (unifI (-1) 0 A).toReal)
    (Z := (unifI 0 1 A).toReal) (W := (unifI (-1) 1 A).toReal) hp0 (by rw [hs1]; ring) (by rw [hs2]; ring)
    (by rw [hs3]; ring) (by rw [hs4]; ring)
  simp only [uv]
  rw [← e]; ring

theorem g_tuples {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 2 / 3) (i : Fin 3) :
    (∀ j, gl 3 i p j ≤ gr 3 i p j) ∧
    (∀ j, 2 * (gr 3 i p j - gl 3 i p j) ≤ ∑ j', (gr 3 i p j' - gl 3 i p j')) ∧
    ∑ j, (gl 3 i p j + gr 3 i p j) = 2 * (((3 : ℕ) : ℝ) * (-p) / 2) := by
  fin_cases i <;>
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩ <;>
  (try fin_cases j) <;>
  simp [gl, gr, Fin.sum_univ_three] <;>
  linarith



/-! ### Lemma 1 with measurable choices -/

/-- The plane of the Archimedes measure `archPlane`. -/
abbrev V2 := EuclideanSpace ℝ (Fin 2)

/-- First unit vector. -/
def eu : V2 := EuclideanSpace.single 0 1
/-- Second unit vector. -/
def ew : V2 := EuclideanSpace.single 1 1

/-- The abscissa of the third vertex of the triangle with sides `a, S, T`. -/
def triX (a S T : ℝ) : ℝ := (a ^ 2 + T ^ 2 - S ^ 2) / (2 * a)
/-- The ordinate of the third vertex. -/
def triY (a S T : ℝ) : ℝ := √(T ^ 2 - triX a S T ^ 2)

/-- `E_k`. -/
def triEk (a : ℝ) : V2 := a • eu
/-- `E_G`. -/
def triEG (a S T : ℝ) : V2 := (triX a S T - a) • eu + triY a S T • ew
/-- `E_H`. -/
def triEH (a S T : ℝ) : V2 := -(triX a S T • eu + triY a S T • ew)

lemma tri_ok {a S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (h : (0 < a ∧ |S - T| ≤ a ∧ a ≤ S + T) ∨ (a = 0 ∧ S = 0 ∧ T = 0)) :
    ‖triEk a‖ = a ∧ ‖triEG a S T‖ = S ∧ ‖triEH a S T‖ = T ∧
      triEk a + triEG a S T + triEH a S T = 0 := by
  rcases h with ⟨ha, h1, h2⟩ | ⟨rfl, rfl, rfl⟩
  · exact triangle_of_orthonormal orthonormal_single_two.1 orthonormal_single_two.2.1
      orthonormal_single_two.2.2 ha hS hT h1 h2
  · simp [triEk, triEG, triEH, triX, triY]

variable {n : ℕ}

/-- A candidate partition `{k} ∪ G ∪ H`. -/
abbrev Cand (n : ℕ) := Fin n × Finset (Fin n) × Finset (Fin n)

/-- The candidate is a partition and the triangle with sides `λ_k, S, T` exists (or all three
are `0`). -/
def CandOK (l r : Fin n → ℝ) (c : Cand n) : Prop :=
  c.1 ∉ c.2.1 ∧ c.1 ∉ c.2.2 ∧ Disjoint c.2.1 c.2.2 ∧ (∀ j, j = c.1 ∨ j ∈ c.2.1 ∨ j ∈ c.2.2) ∧
    ((0 < r c.1 - l c.1 ∧ |∑ j ∈ c.2.1, (r j - l j) - ∑ j ∈ c.2.2, (r j - l j)| ≤ r c.1 - l c.1 ∧
        r c.1 - l c.1 ≤ ∑ j ∈ c.2.1, (r j - l j) + ∑ j ∈ c.2.2, (r j - l j)) ∨
      (r c.1 - l c.1 = 0 ∧ ∑ j ∈ c.2.1, (r j - l j) = 0 ∧ ∑ j ∈ c.2.2, (r j - l j) = 0))

/-- The vector of Lemma 1 for a candidate. -/
def candVec (l r : Fin n → ℝ) (c : Cand n) (ξ : V2) : Fin n → ℝ :=
  archVec l r c.1 c.2.1 c.2.2 (triEk (r c.1 - l c.1))
    (triEG (r c.1 - l c.1) (∑ j ∈ c.2.1, (r j - l j)) (∑ j ∈ c.2.2, (r j - l j)))
    (triEH (r c.1 - l c.1) (∑ j ∈ c.2.1, (r j - l j)) (∑ j ∈ c.2.2, (r j - l j))) ξ

/-- The vector of the first good candidate of a list. -/
def firstVec (l r : Fin n → ℝ) (L : List (Cand n)) (ξ : V2) : Fin n → ℝ :=
  L.foldr (fun c acc => if CandOK l r c then candVec l r c ξ else acc) 0

lemma firstVec_spec (l r : Fin n → ℝ) (L : List (Cand n)) (h : ∃ c ∈ L, CandOK l r c) :
    ∃ c, CandOK l r c ∧ ∀ ξ, firstVec l r L ξ = candVec l r c ξ := by
  induction L with
  | nil => simp at h
  | cons c L ih =>
    by_cases hc : CandOK l r c
    · exact ⟨c, hc, fun ξ => by simp [firstVec, hc]⟩
    · obtain ⟨c', hc'L, hc'⟩ := h
      have : c' ∈ L := by
        rcases List.mem_cons.1 hc'L with rfl | h
        · exact absurd hc' hc
        · exact h
      obtain ⟨d, hd, hdv⟩ := ih ⟨c', this, hc'⟩
      exact ⟨d, hd, fun ξ => by simp only [firstVec, List.foldr_cons, hc, ite_false]; exact hdv ξ⟩

lemma candVec_jointMix {l r : Fin n → ℝ} (hle : ∀ j, l j ≤ r j) {c : Cand n}
    (hc : CandOK l r c) :
    IsJointMix (fun j => unifI (l j) (r j)) (archPlane.map (candVec l r c)) ∧
      ∀ᵐ x ∂(archPlane.map (candVec l r c)), ∑ j, x j = 1 / 2 * ∑ j, (l j + r j) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  have hS : 0 ≤ ∑ j ∈ c.2.1, (r j - l j) := Finset.sum_nonneg fun j _ => sub_nonneg.2 (hle j)
  have hT : 0 ≤ ∑ j ∈ c.2.2, (r j - l j) := Finset.sum_nonneg fun j _ => sub_nonneg.2 (hle j)
  obtain ⟨e1, e2, e3, e4⟩ := tri_ok hS hT h5
  exact arch_of_partition isArchimedesMeasure_archPlane l r hle c.1 c.2.1 c.2.2 h1 h2 h3 h4
    _ _ _ e1 e2 e3 e4

/-- Every tuple of intervals with the polygon inequality has a good candidate. -/
lemma exists_candOK {l r : Fin n → ℝ} (hn : 0 < n) (hle : ∀ j, l j ≤ r j)
    (hpoly : ∀ j, 2 * (r j - l j) ≤ ∑ i, (r i - l i)) : ∃ c : Cand n, CandOK l r c := by
  by_cases hpos : ∃ j, l j < r j
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => r j - l j) hne
    set L := (Finset.univ.erase k).toList
    have hL : L.Nodup := Finset.nodup_toList _
    have hLk : ∀ j, j ∈ L ↔ j ≠ k := fun j => by simp [L]
    let g : ℕ → ℝ := fun s' => |2 * ((L.take s').map fun j => r j - l j).sum -
      ∑ j ∈ Finset.univ.erase k, (r j - l j)|
    obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (Finset.range (L.length + 1)) g
      ⟨0, by simp⟩
    have hs' : s ≤ L.length := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    obtain ⟨hb1, hb2, -⟩ := lem_arch isArchimedesMeasure_archPlane orthonormal_single_two.1
      orthonormal_single_two.2.1 orthonormal_single_two.2.2 l r hle hpos hpoly k
      (fun j => hk j (Finset.mem_univ j)) L hL hLk s hs'
      (fun s' hs'' => hmin s' (Finset.mem_range.2 (Nat.lt_succ_of_le hs'')))
    have hkpos : 0 < r k - l k := by
      obtain ⟨j, hj⟩ := hpos
      exact lt_of_lt_of_le (sub_pos.2 hj) (hk j (Finset.mem_univ j))
    have hdisj := List.disjoint_take_drop hL (le_refl s)
    refine ⟨(k, (L.take s).toFinset, (L.drop s).toFinset), ?_, ?_, ?_, ?_, Or.inl ⟨hkpos, hb1, hb2⟩⟩
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
  · push Not at hpos
    have h0 : ∀ j, r j - l j = 0 := fun j => by linarith [hle j, hpos j]
    refine ⟨(⟨0, hn⟩, ∅, Finset.univ.erase ⟨0, hn⟩), by simp, by simp, by simp, ?_, Or.inr ?_⟩
    · intro j; by_cases h : j = ⟨0, hn⟩ <;> simp [h]
    · simp [h0]

/-- The joint mix of Lemma 1 for a tuple depending on a parameter `γ`, as a function of
`(γ, ξ)`. -/
def jmVec (l r : ℝ → Fin n → ℝ) (p : ℝ × V2) : Fin n → ℝ :=
  firstVec (l p.1) (r p.1) (Finset.univ : Finset (Cand n)).toList p.2

/-- The law of `jmVec` for a fixed parameter. -/
def jmK (l r : ℝ → Fin n → ℝ) (γ : ℝ) : Measure (Fin n → ℝ) :=
  archPlane.map fun ξ => jmVec l r (γ, ξ)

lemma measurable_triX {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) : Measurable fun γ => triX (f γ) (g γ) (h γ) := by
  unfold triX; fun_prop

lemma measurable_triY {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) : Measurable fun γ => triY (f γ) (g γ) (h γ) := by
  unfold triY
  exact (((hh.pow_const 2).sub ((measurable_triX hf hg hh).pow_const 2))).sqrt

lemma measurable_candVec {l r : ℝ → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (c : Cand n) : Measurable fun p : ℝ × V2 => candVec (l p.1) (r p.1) c p.2 := by
  have hl' : ∀ j, Measurable fun p : ℝ × V2 => l p.1 j :=
    fun j => (measurable_pi_apply j).comp (hl.comp measurable_fst)
  have hr' : ∀ j, Measurable fun p : ℝ × V2 => r p.1 j :=
    fun j => (measurable_pi_apply j).comp (hr.comp measurable_fst)
  have ha : Measurable fun p : ℝ × V2 => r p.1 c.1 - l p.1 c.1 := (hr' _).sub (hl' _)
  have hS : ∀ G : Finset (Fin n), Measurable fun p : ℝ × V2 => ∑ j ∈ G, (r p.1 j - l p.1 j) :=
    fun G => Finset.measurable_sum _ fun j _ => (hr' j).sub (hl' j)
  have hx := measurable_triX ha (hS c.2.1) (hS c.2.2)
  have hy := measurable_triY ha (hS c.2.1) (hS c.2.2)
  have hEk : Measurable fun p : ℝ × V2 => triEk (r p.1 c.1 - l p.1 c.1) := by
    unfold triEk; exact ha.smul_const _
  have hEG : Measurable fun p : ℝ × V2 => triEG (r p.1 c.1 - l p.1 c.1)
      (∑ j ∈ c.2.1, (r p.1 j - l p.1 j)) (∑ j ∈ c.2.2, (r p.1 j - l p.1 j)) := by
    unfold triEG; exact ((hx.sub ha).smul_const _).add (hy.smul_const _)
  have hEH : Measurable fun p : ℝ × V2 => triEH (r p.1 c.1 - l p.1 c.1)
      (∑ j ∈ c.2.1, (r p.1 j - l p.1 j)) (∑ j ∈ c.2.2, (r p.1 j - l p.1 j)) := by
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

lemma measurableSet_candOK {l r : ℝ → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (c : Cand n) : MeasurableSet {γ | CandOK (l γ) (r γ) c} := by
  have hl' : ∀ j, Measurable fun γ => l γ j := fun j => (measurable_pi_apply j).comp hl
  have hr' : ∀ j, Measurable fun γ => r γ j := fun j => (measurable_pi_apply j).comp hr
  have ha : Measurable fun γ => r γ c.1 - l γ c.1 := (hr' _).sub (hl' _)
  have hS : ∀ G : Finset (Fin n), Measurable fun γ => ∑ j ∈ G, (r γ j - l γ j) :=
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

lemma measurable_firstVec {l r : ℝ → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    (L : List (Cand n)) : Measurable fun p : ℝ × V2 => firstVec (l p.1) (r p.1) L p.2 := by
  induction L with
  | nil => exact measurable_const
  | cons c L ih =>
    simp only [firstVec, List.foldr_cons]
    exact Measurable.ite (measurable_fst (measurableSet_candOK hl hr c)) (measurable_candVec hl hr c) ih

lemma measurable_jmVec {l r : ℝ → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r) :
    Measurable (jmVec l r) := measurable_firstVec hl hr _

instance : IsProbabilityMeasure archPlane := isArchimedesMeasure_archPlane.1

lemma measurable_jmK_apply {l r : ℝ → Fin n → ℝ} (hl : Measurable l) (hr : Measurable r)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) : Measurable fun γ => jmK l r γ s := by
  have hm := measurable_jmVec hl hr
  have : (fun γ => jmK l r γ s) = fun γ => archPlane (Prod.mk γ ⁻¹' (jmVec l r ⁻¹' s)) := by
    funext γ
    have hm' : Measurable fun ξ : V2 => jmVec l r (γ, ξ) := hm.comp measurable_prodMk_left
    rw [jmK, Measure.map_apply hm' hs]; rfl
  rw [this]
  exact measurable_measure_prodMk_left (hm hs)

lemma jmK_spec {l r : ℝ → Fin n → ℝ} (hn : 0 < n) {γ : ℝ} (hle : ∀ j, l γ j ≤ r γ j)
    (hpoly : ∀ j, 2 * (r γ j - l γ j) ≤ ∑ i, (r γ i - l γ i)) :
    IsJointMix (fun j => unifI (l γ j) (r γ j)) (jmK l r γ) ∧
      ∀ᵐ x ∂(jmK l r γ), ∑ j, x j = 1 / 2 * ∑ j, (l γ j + r γ j) := by
  obtain ⟨c, hc⟩ := exists_candOK hn hle hpoly
  obtain ⟨d, hd, hdv⟩ := firstVec_spec (l γ) (r γ) (Finset.univ : Finset (Cand n)).toList
    ⟨c, Finset.mem_toList.2 (Finset.mem_univ c), hc⟩
  have : jmK l r γ = archPlane.map (candVec (l γ) (r γ) d) := by
    rw [jmK]; congr 1; funext ξ; exact hdv ξ
  rw [this]
  exact candVec_jointMix hle hd

/-! ### Finite mixtures of tuples depending on a parameter -/

/-- Choose the tuple `i` with probability `w i γ`, draw the joint mix of Lemma 1 for it and
permute the coordinates uniformly at random (Lemma 3). -/
def mixK {ι : Type*} [Fintype ι] (w : ι → ℝ → ℝ) (l r : ι → ℝ → Fin n → ℝ) (γ : ℝ) :
    Measure (Fin n → ℝ) :=
  mixture (fun i => ENNReal.ofReal (w i γ)) fun i => permAvg (jmK (l i) (r i) γ)

lemma measurable_mixK {ι : Type*} [Fintype ι] {w : ι → ℝ → ℝ} {l r : ι → ℝ → Fin n → ℝ}
    (hw : ∀ i, Measurable (w i)) (hl : ∀ i, Measurable (l i)) (hr : ∀ i, Measurable (r i)) :
    Measurable (mixK w l r) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [mixK, mixture, permAvg, sum_apply, smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun i _ => (hw i).ennreal_ofReal.mul
    (measurable_const.mul (Finset.measurable_sum _ fun π _ => ?_))
  have : (fun γ => (jmK (l i) (r i) γ).map (fun x => x ∘ π) s) =
      fun γ => jmK (l i) (r i) γ ((fun x => x ∘ π) ⁻¹' s) := by
    funext γ; rw [Measure.map_apply (measurable_comp_perm π) hs]
  rw [this]
  exact measurable_jmK_apply (hl i) (hr i) (measurable_comp_perm π hs)

lemma mixK_spec {ι : Type*} [Fintype ι] {w : ι → ℝ → ℝ} {l r : ι → ℝ → Fin n → ℝ}
    (hn : 0 < n) {γ : ℝ} (hw0 : ∀ i, 0 ≤ w i γ) (hw1 : ∑ i, w i γ = 1)
    (hle : ∀ i j, l i γ j ≤ r i γ j)
    (hpoly : ∀ i j, 2 * (r i γ j - l i γ j) ≤ ∑ j', (r i γ j' - l i γ j')) (s : ℝ)
    (hs : ∀ i, ∑ j, (l i γ j + r i γ j) = 2 * s) :
    IsCompleteMix n (∑ i, ENNReal.ofReal (w i γ) •
        ((n : ℝ≥0∞)⁻¹ • ∑ j, unifI (l i γ j) (r i γ j))) (mixK w l r γ) ∧
      ∀ᵐ x ∂(mixK w l r γ), ∑ j, x j = s := by
  have hw : ∑ i, ENNReal.ofReal (w i γ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw0 i, hw1, ENNReal.ofReal_one]
  refine lem_sym _ hw (fun i j => unifI (l i γ j) (r i γ j)) _ s
    (fun i => (jmK_spec hn (hle i) (hpoly i)).1) fun i => ?_
  filter_upwards [(jmK_spec hn (hle i) (hpoly i)).2] with x hx
  rw [hx, hs i]; ring


/-! ### Measurability of the families -/

lemma measurable_kl {N : ℕ} {A B : ℝ → ℕ} {L : ℝ → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hL : Measurable L) (j : ℕ) : Measurable fun p => kl N (A p) (B p) (L p) j := by
  unfold kl
  refine Measurable.ite (hA (MeasurableSet.of_discrete : MeasurableSet {k : ℕ | j < k}))
    measurable_const (Measurable.ite ((hA.add hB) (MeasurableSet.of_discrete :
      MeasurableSet {k : ℕ | j < k})) measurable_const
      (Measurable.ite (MeasurableSet.const _) measurable_const hL))

lemma measurable_kr {N : ℕ} {A B : ℝ → ℕ} {R : ℝ → ℝ} (hA : Measurable A) (hB : Measurable B)
    (hR : Measurable R) (j : ℕ) : Measurable fun p => kr N (A p) (B p) (R p) j := by
  unfold kr
  refine Measurable.ite (hA (MeasurableSet.of_discrete : MeasurableSet {k : ℕ | j < k}))
    measurable_const (Measurable.ite ((hA.add hB) (MeasurableSet.of_discrete :
      MeasurableSet {k : ℕ | j < k})) measurable_const
      (Measurable.ite (MeasurableSet.const _) measurable_const hR))

lemma measurableSet_fII (N : ℕ) : MeasurableSet {p | fII N p} := by
  unfold fII fK; exact measurableSet_lt measurable_const (by fun_prop)

lemma measurable_fc (N : ℕ) : Measurable (fc N) := by
  unfold fc
  refine Measurable.ite (measurableSet_fII N) measurable_const ?_
  exact ((Nat.measurable_floor.comp (by unfold fK; fun_prop)).add measurable_const).min
    measurable_const

lemma measurable_fb (N : ℕ) : Measurable (fb N) :=
  Measurable.ite (measurableSet_fII N) measurable_const measurable_const

lemma measurable_fa (N : ℕ) : Measurable (fa N) := by
  unfold fa
  exact (measurable_const.sub (measurable_fb N)).sub (measurable_fc N)

lemma measurable_fα (N : ℕ) : Measurable (fα N) := by
  unfold fα
  refine Measurable.ite (measurableSet_fII N) (by unfold fK; fun_prop) ?_
  exact ((by unfold fK; fun_prop : Measurable (fK N)).sub
    ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp (measurable_fc N))).add
    measurable_const

lemma measurable_fl (m : ℕ) (i : Fin 2) : Measurable (fl m i) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold fl
  by_cases hi : i = 0
  · simp only [hi, if_true]
    exact measurable_kl (measurable_fa _) (measurable_fb _) measurable_const _
  · simp only [hi, if_false]
    exact measurable_kl ((measurable_fa _).add measurable_const) (measurable_fb _)
      ((measurable_fα _).sub measurable_const) _

lemma measurable_fr (m : ℕ) (i : Fin 2) : Measurable (fr m i) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold fr
  by_cases hi : i = 0
  · simp only [hi, if_true]
    exact measurable_kr (measurable_fa _) (measurable_fb _) ((measurable_fα _).sub measurable_const) _
  · simp only [hi, if_false]
    exact measurable_kr ((measurable_fa _).add measurable_const) (measurable_fb _)
      measurable_const _

lemma measurable_fw (N : ℕ) (i : Fin 2) : Measurable (fw N i) := by
  unfold fw; split_ifs
  · exact measurable_fα N
  · exact measurable_const.sub (measurable_fα N)

lemma measurable_gl (m : ℕ) (i : Fin 3) : Measurable (gl m i) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold gl; split_ifs <;> fun_prop

lemma measurable_gr (m : ℕ) (i : Fin 3) : Measurable (gr m i) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold gr; split_ifs <;> fun_prop

lemma measurable_gw (i : Fin 3) : Measurable (gw i) := by
  unfold gw; split_ifs <;> fun_prop

/-! ### Affine images of complete mixes -/

lemma isCompleteMix_map_affine {n : ℕ} {F : Measure ℝ} {P : Measure (Fin n → ℝ)}
    (hP : IsCompleteMix n F P) (a b s : ℝ) (hs : ∀ᵐ x ∂P, ∑ j, x j = s) :
    IsCompleteMix n (F.map fun t => a * t + b) (P.map fun x j => a * x j + b) ∧
      ∀ᵐ y ∂(P.map fun x j => a * x j + b), ∑ j, y j = a * s + n * b := by
  obtain ⟨hprob, -, hmarg⟩ := hP
  have hf : Measurable fun x : Fin n → ℝ => fun j => a * x j + b :=
    measurable_pi_iff.2 fun j => (measurable_const.mul (measurable_pi_apply j)).add
      measurable_const
  have hsum : ∀ᵐ y ∂(P.map fun x j => a * x j + b), ∑ j, y j = a * s + n * b := by
    rw [ae_map_iff hf.aemeasurable (measurableSet_sum_eq _)]
    filter_upwards [hs] with x hx
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx]; simp
  refine ⟨⟨inferInstance, ⟨_, hsum⟩, fun j => ?_⟩, hsum⟩
  rw [Measure.map_map (measurable_pi_apply j) hf]
  show _ = Measure.map _ F
  have hm := hmarg j
  simp only at hm
  rw [← hm, Measure.map_map (by fun_prop : Measurable fun t : ℝ => a * t + b)
    (measurable_pi_apply j)]
  rfl

lemma tilt_map_neg {p : ℝ} (hp : |p| ≤ 1) :
    (tilt 1 (-p)).map (fun t => -1 * t + 0) = tilt 1 p := by
  have hf : (fun t : ℝ => -1 * t + 0) = fun t => 0 - t := by funext t; ring
  rw [tilt_eq one_pos (by rwa [abs_neg]), tilt_eq one_pos hp, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul, Measure.map_smul, hf, JointSplit.map_reflect_unifI (by norm_num),
    JointSplit.map_reflect_unifI (by norm_num), add_comm]
  · norm_num [← sub_eq_add_neg]
  all_goals fun_prop

lemma tilt_map_mul {H γ : ℝ} (hH : 0 < H) (hγ : |γ| ≤ 1) :
    (tilt 1 γ).map (fun t => H * t + 0) = tilt H γ := by
  have hf : (fun t : ℝ => H * t + 0) = fun t => H * t := by funext t; ring
  rw [tilt_eq one_pos hγ, tilt_eq hH hγ, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul, Measure.map_smul, hf, map_mul_unifI hH (by norm_num),
    map_mul_unifI hH (by norm_num)]
  · norm_num
  all_goals fun_prop

/-! ### The kernel of Lemma `as:lem:tilt` -/

/-- The largest admissible `p = -γ`: `2/3` for `m = 3`, `1` otherwise. -/
def pmax (m : ℕ) : ℝ := if m = 3 then 2 / 3 else 1

/-- `p` clamped into `[0, pmax m]`. -/
def clampP (m : ℕ) (p : ℝ) : ℝ := max 0 (min p (pmax m))

lemma clampP_mem (m : ℕ) (p : ℝ) : 0 ≤ clampP m p ∧ clampP m p ≤ pmax m := by
  have : 0 < pmax m := by unfold pmax; split_ifs <;> norm_num
  unfold clampP
  exact ⟨le_max_left _ _, max_le this.le (min_le_right _ _)⟩

lemma clampP_eq {m : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ pmax m) : clampP m p = p := by
  unfold clampP; rw [min_eq_left h1, max_eq_right h0]

lemma measurable_clampP (m : ℕ) : Measurable (clampP m) := by
  unfold clampP; fun_prop

/-- The complete mix of `P_{1,-p}` for `p ∈ [0, pmax m]` (clamped outside). -/
def K0 (m : ℕ) (p : ℝ) : Measure (Fin m → ℝ) :=
  if m = 3 then mixK gw (gl m) (gr m) (clampP m p)
  else mixK (fw (m - 1)) (fl m) (fr m) (clampP m p)

lemma measurable_K0 (m : ℕ) : Measurable (K0 m) := by
  unfold K0
  split_ifs
  · exact (measurable_mixK measurable_gw (measurable_gl m) (measurable_gr m)).comp
      (measurable_clampP m)
  · exact (measurable_mixK (measurable_fw _) (measurable_fl m) (measurable_fr m)).comp
      (measurable_clampP m)

lemma K0_spec {m : ℕ} (hm : 3 ≤ m) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ pmax m) :
    IsCompleteMix m (tilt 1 (-p)) (K0 m p) ∧ ∀ᵐ x ∂(K0 m p), ∑ j, x j = m * (-p) / 2 := by
  unfold K0
  rw [clampP_eq h0 h1]
  split_ifs with h3
  · subst h3
    have hp : p ≤ 2 / 3 := by simpa [pmax] using h1
    have := mixK_spec (w := gw) (l := gl 3) (r := gr 3) (by norm_num) (gw_nonneg h0 (by linarith))
      (by simp [Fin.sum_univ_three, gw]; ring) (fun i => (g_tuples h0 hp i).1)
      (fun i => (g_tuples h0 hp i).2.1) _ (fun i => (g_tuples h0 hp i).2.2)
    rwa [g_marg h0 hp] at this
  · obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
    have hN : 3 ≤ N := by omega
    have hp : p ≤ 1 := by simpa [pmax, h3] using h1
    simp only [Nat.add_sub_cancel]
    have := mixK_spec (w := fw N) (l := fl (N + 1)) (r := fr (N + 1)) (by omega)
      (fw_nonneg hN h0 hp) (by simp [Fin.sum_univ_two, fw])
      (fun i => (f_tuples hN h0 hp i).1) (fun i => (f_tuples hN h0 hp i).2.1) _
      (fun i => (f_tuples hN h0 hp i).2.2)
    rwa [f_marg hN h0 hp] at this

lemma isProb_K0 {m : ℕ} (hm : 3 ≤ m) (p : ℝ) : IsProbabilityMeasure (K0 m p) := by
  have h : K0 m p = K0 m (clampP m p) := by
    unfold K0; rw [clampP_eq (clampP_mem m p).1 (clampP_mem m p).2]
  rw [h]
  exact (K0_spec hm (clampP_mem m p).1 (clampP_mem m p).2).1.1

/-- The kernel of Lemma `as:lem:tilt` for `H = 1`: for `γ ≤ 0` the complete mix `K0 m (-γ)`,
for `γ > 0` its reflection. -/
def tiltK (m : ℕ) (γ : ℝ) : Measure (Fin m → ℝ) :=
  if γ ≤ 0 then K0 m (-γ) else (K0 m γ).map fun x j => -1 * x j + 0

lemma measurable_tiltK (m : ℕ) : Measurable (tiltK m) := by
  unfold tiltK
  refine Measurable.ite (measurableSet_le measurable_id measurable_const)
    ((measurable_K0 m).comp measurable_neg) ?_
  exact (Measure.measurable_map _ (measurable_pi_iff.2 fun j =>
    (measurable_const.mul (measurable_pi_apply j)).add measurable_const)).comp (measurable_K0 m)

lemma isProb_tiltK {m : ℕ} (hm : 3 ≤ m) (γ : ℝ) : IsProbabilityMeasure (tiltK m γ) := by
  unfold tiltK
  split_ifs
  · exact isProb_K0 hm _
  · have := isProb_K0 hm γ
    infer_instance

lemma tiltRange_iff {m : ℕ} {γ : ℝ} (h : TiltRange m γ) : 3 ≤ m ∧ |γ| ≤ pmax m := by
  rcases h with ⟨h1, h2⟩ | ⟨rfl, h2⟩
  · exact ⟨by omega, by simpa [pmax, show m ≠ 3 by omega] using h2⟩
  · exact ⟨le_rfl, by simpa [pmax] using h2⟩

lemma pmax_le_one (m : ℕ) : pmax m ≤ 1 := by unfold pmax; split_ifs <;> norm_num

theorem tiltK_spec {m : ℕ} {γ : ℝ} (h : TiltRange m γ) :
    IsCompleteMix m (tilt 1 γ) (tiltK m γ) ∧ ∀ᵐ x ∂(tiltK m γ), ∑ j, x j = m * γ / 2 := by
  obtain ⟨hm, hγ⟩ := tiltRange_iff h
  have hγ' := abs_le.1 hγ
  unfold tiltK
  split_ifs with h0
  · have := K0_spec hm (p := -γ) (by linarith) (by linarith)
    simp only [neg_neg] at this; exact this
  · have hK := K0_spec hm (p := γ) (by linarith) (by linarith)
    have := isCompleteMix_map_affine hK.1 (-1) 0 _ hK.2
    rw [tilt_map_neg (by linarith [pmax_le_one m] : |γ| ≤ 1)] at this
    refine ⟨this.1, this.2.mono fun x hx => ?_⟩
    rw [hx]; ring

/-- **Lemma `as:lem:tilt`**, with a measurable family: for `H > 0` the complete mixes of
`P_{H,γ}` (sum `m γ H / 2`) form a measurable kernel `γ ↦ tiltKH m H γ` of probability
measures. -/
def tiltKH (m : ℕ) (H γ : ℝ) : Measure (Fin m → ℝ) := (tiltK m γ).map fun x j => H * x j + 0

lemma measurable_tiltKH (m : ℕ) (H : ℝ) : Measurable (tiltKH m H) :=
  (Measure.measurable_map _ (measurable_pi_iff.2 fun j =>
    (measurable_const.mul (measurable_pi_apply j)).add measurable_const)).comp (measurable_tiltK m)

lemma isProb_tiltKH {m : ℕ} (hm : 3 ≤ m) (H γ : ℝ) : IsProbabilityMeasure (tiltKH m H γ) := by
  have := isProb_tiltK hm γ
  unfold tiltKH; infer_instance

theorem tiltKH_spec {m : ℕ} {H γ : ℝ} (hH : 0 < H) (h : TiltRange m γ) :
    IsCompleteMix m (tilt H γ) (tiltKH m H γ) ∧
      ∀ᵐ x ∂(tiltKH m H γ), ∑ j, x j = m * γ * H / 2 := by
  obtain ⟨hm, hγ⟩ := tiltRange_iff h
  have hK := tiltK_spec h
  have := isCompleteMix_map_affine hK.1 H 0 _ hK.2
  rw [tilt_map_mul hH (hγ.trans (pmax_le_one m))] at this
  refine ⟨this.1, this.2.mono fun x hx => ?_⟩
  rw [hx]; ring

/-- **Lemma `as:lem:tilt`**. -/
theorem lemTilt : LemTilt := fun _ _ _ hH h => ⟨_, tiltKH_spec hH h⟩


/-! ### Mixtures of tilts: the identity `as:eq:affine` -/

/-- `ofReal((1-γ)/2) U[-H,0] + ofReal((1+γ)/2) U[0,H]`, equal to `P_{H,γ}` for `|γ| ≤ 1`. -/
def tiltLin (H γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 - γ) / 2) • unifI (-H) 0 + ENNReal.ofReal ((1 + γ) / 2) • unifI 0 H

lemma measurable_tiltLin (H : ℝ) : Measurable (tiltLin H) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [tiltLin, add_apply, smul_apply, smul_eq_mul]
  fun_prop

lemma bind_congr_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {f g : α → Measure β} (h : f =ᵐ[ν] g) : ν.bind f = ν.bind g := by
  unfold Measure.bind; rw [Measure.map_congr h]

lemma integrable_of_abs_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ᵐ t ∂ν, |g t| ≤ C) : Integrable g ν :=
  (integrable_const C).mono' hg.aestronglyMeasurable
    (hC.mono fun t ht => by rwa [Real.norm_eq_abs])

lemma bind_tiltLin (H : ℝ) {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {g : X → ℝ}
    (hg : Measurable g) (hb : ∀ᵐ t ∂ν, |g t| ≤ 1) :
    ν.bind (fun t => tiltLin H (g t)) = tiltLin H (∫ t, g t ∂ν) := by
  have hi := integrable_of_abs_le hg hb
  have key : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∫⁻ t, ENNReal.ofReal ((1 + σ * g t) / 2) ∂ν =
      ENNReal.ofReal ((1 + σ * ∫ t, g t ∂ν) / 2) := by
    intro σ hσ
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_div, integral_add (integrable_const _) (hi.const_mul σ), integral_const,
        integral_const_mul]
      simp
    · exact ((integrable_const 1).add (hi.const_mul σ)).div_const 2
    · filter_upwards [hb] with t ht
      have := abs_le.1 ht
      rcases hσ with rfl | rfl <;> exact div_nonneg (by linarith [this.1, this.2]) (by norm_num)
  ext s hs
  have hmeas : Measurable fun t => tiltLin H (g t) := (measurable_tiltLin H).comp hg
  rw [Measure.bind_apply hs hmeas.aemeasurable]
  simp only [tiltLin, add_apply, smul_apply, smul_eq_mul]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop)]
  have k1 := key (-1) (Or.inr rfl)
  have k2 := key 1 (Or.inl rfl)
  simp only [neg_one_mul, one_mul, ← sub_eq_add_neg] at k1 k2
  rw [k1, k2]

lemma tilt_eq_tiltLin {H γ : ℝ} (hH : 0 < H) (hγ : |γ| ≤ 1) : tilt H γ = tiltLin H γ :=
  tilt_eq hH hγ

/-- **The identity `as:eq:affine`**: for a probability measure `ρ` carried by `[-1,1]`,
`∫ P_{H,γ} ρ(dγ) = P_{H, γ̄}` with `γ̄ = ∫ γ ρ(dγ)`. -/
theorem eq_affine {H : ℝ} (hH : 0 < H) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ γ ∂ρ, |γ| ≤ 1) : ρ.bind (tilt H) = tilt H (∫ γ, γ ∂ρ) := by
  have hb : |∫ γ, γ ∂ρ| ≤ 1 := by
    have := integrable_of_abs_le measurable_id hρ
    refine abs_le.2 ⟨?_, ?_⟩
    · have := integral_mono_ae (integrable_const (-1 : ℝ)) this
        (hρ.mono fun γ h => (abs_le.1 h).1)
      simpa using this
    · have := integral_mono_ae this (integrable_const (1 : ℝ))
        (hρ.mono fun γ h => (abs_le.1 h).2)
      simpa using this
  have e : ρ.bind (tilt H) = ρ.bind (fun γ => tiltLin H (id γ)) :=
    bind_congr_ae (hρ.mono fun γ h => tilt_eq hH h)
  rw [e, bind_tiltLin H measurable_id hρ, tilt_eq hH hb]
  rfl

/-! ### Point masses and sums -/

lemma map_eq_dirac {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {c : ℝ} (h : ∀ᵐ x ∂μ, f x = c) : μ.map f = Measure.dirac c := by
  rw [Measure.map_congr (g := fun _ => c) h, Measure.map_const, measure_univ, one_smul]

lemma tiltLin_zero_map {c H : ℝ} (hH : 0 < H) :
    (tiltLin 1 0).map (fun s => H * s + c) = unifI (c - H) (c + H) := by
  have h1 : tiltLin 1 0 = unifI (-1) 1 := by
    rw [unifI_split' (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num) (by norm_num), tiltLin]
    norm_num
  have hf : (fun s : ℝ => H * s + c) = (fun t => c + t) ∘ (fun s => H * s) := by
    funext s; simp [add_comm]
  rw [h1, hf, ← Measure.map_map (measurable_const_add c) (measurable_const_mul H),
    map_mul_unifI hH (by norm_num), map_unifI_const_add]
  congr 1 <;> ring

/-! ### Proposition `as:prop:window` for `d = 1` -/

/-- The kernel of the window: given the sum `t`, the affine image of the tilt kernel at
`γ = 2(t - m c)/(m H)`. -/
def winK (m : ℕ) (c H : ℝ) (t : ℝ) : Measure (Fin m → ℝ) :=
  (tiltK m (2 * (t - m * c) / (m * H))).map fun x j => H * x j + c

lemma measurable_winK (m : ℕ) (c H : ℝ) : Measurable (winK m c H) :=
  (Measure.measurable_map _ (measurable_pi_iff.2 fun j =>
    (measurable_const.mul (measurable_pi_apply j)).add measurable_const)).comp
    ((measurable_tiltK m).comp (by fun_prop))

lemma winK_spec {m : ℕ} {c H t : ℝ} (hH : 0 < H)
    (h : TiltRange m (2 * (t - m * c) / (m * H))) :
    IsCompleteMix m ((tilt 1 (2 * (t - m * c) / (m * H))).map fun s => H * s + c) (winK m c H t) ∧
      ∀ᵐ x ∂(winK m c H t), ∑ j, x j = t := by
  have hm : (0 : ℝ) < m := by
    obtain ⟨hm, -⟩ := tiltRange_iff h; exact_mod_cast (by omega : 0 < m)
  have hK := tiltK_spec h
  have := isCompleteMix_map_affine hK.1 H c _ hK.2
  refine ⟨this.1, this.2.mono fun x hx => ?_⟩
  rw [hx]; field_simp; ring

/-- **Proposition `as:prop:window`, `d = 1`, general form**: if `ν` has mean `m c` and
`TiltRange m γ` holds `ν`-a.e. for `γ = 2(t - m c)/(m H)`, then the law of the tuple drawn from
`winK m c H t` given `t ∼ ν` has marginals `U[c-H, c+H]` and sum `∼ ν`. -/
theorem window_one {m : ℕ} {c H : ℝ} (hH : 0 < H) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hr : ∀ᵐ t ∂ν, TiltRange m (2 * (t - m * c) / (m * H))) (hmean : ∫ t, t ∂ν = m * c) :
    IsProbabilityMeasure (ν.bind (winK m c H)) ∧
      (∀ j, (ν.bind (winK m c H)).map (fun x => x j) = unifI (c - H) (c + H)) ∧
      (ν.bind (winK m c H)).map (fun x => ∑ j, x j) = ν := by
  have hm3 : 3 ≤ m := by
    obtain ⟨t, ht⟩ := hr.exists; exact (tiltRange_iff ht).1
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set g : ℝ → ℝ := fun t => 2 * (t - m * c) / (m * H) with hg_def
  have hgm : Measurable g := by fun_prop
  have hgb : ∀ᵐ t ∂ν, |g t| ≤ 1 := hr.mono fun t ht =>
    ((tiltRange_iff ht).2).trans (pmax_le_one m)
  have hwk := measurable_winK m c H
  have hprob : ∀ t, IsProbabilityMeasure (winK m c H t) := fun t => by
    have := isProb_tiltK hm3 (g t); unfold winK; infer_instance
  refine ⟨⟨?_⟩, fun j => ?_, ?_⟩
  · rw [Measure.bind_apply MeasurableSet.univ hwk.aemeasurable]
    simp
  · rw [Measure.map_bind hwk.aemeasurable (measurable_pi_apply j).aemeasurable]
    have h1 : (fun t => (winK m c H t).map (fun x => x j)) =ᵐ[ν]
        fun t => (tiltLin 1 (g t)).map (fun s => H * s + c) := by
      filter_upwards [hr, hgb] with t ht hb
      rw [(winK_spec hH ht).1.2.2 j, tilt_eq one_pos hb]
      rfl
    have hmeas : Measurable fun t => tiltLin 1 (g t) := (measurable_tiltLin 1).comp hgm
    rw [bind_congr_ae h1, ← Measure.map_bind hmeas.aemeasurable
      (by fun_prop : Measurable fun s : ℝ => H * s + c).aemeasurable,
      bind_tiltLin 1 hgm hgb]
    have hint : ∫ t, g t ∂ν = 0 := by
      have hid : Integrable (fun t : ℝ => t) ν := by
        have : Integrable g ν := integrable_of_abs_le hgm hgb
        have e : (fun t : ℝ => t) = fun t => (m * H / 2) * g t + m * c := by
          funext t; simp only [hg_def]; field_simp; ring
        rw [e]; exact (this.const_mul _).add (integrable_const _)
      simp only [hg_def]
      rw [integral_div, integral_const_mul, integral_sub hid (integrable_const _), hmean,
        integral_const]
      simp
    rw [hint, tiltLin_zero_map hH]
  · rw [Measure.map_bind hwk.aemeasurable
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).aemeasurable]
    have h1 : (fun t => (winK m c H t).map (fun x => ∑ j, x j)) =ᵐ[ν] Measure.dirac := by
      filter_upwards [hr] with t ht
      exact map_eq_dirac (winK_spec hH ht).2
    rw [bind_congr_ae h1, Measure.bind_dirac]

lemma inAgg_of_window_one {m : ℕ} {c H : ℝ} (hH : 0 < H) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hr : ∀ᵐ t ∂ν, TiltRange m (2 * (t - m * c) / (m * H)))
    (hmean : ∫ t, t ∂ν = m * c) : InAgg (fun _ : Fin m => unifI (c - H) (c + H)) ν :=
  let h := window_one hH hr hmean
  ⟨_, h.1, h.2.1, h.2.2⟩

/-- **Proposition `as:prop:window`, `d = 1`, `m ≥ 4`**. -/
theorem propWindowReal : PropWindowReal := by
  intro m c H ν hH hm hν hsupp hmean
  refine inAgg_of_window_one hH (hsupp.mono fun t ht => Or.inl ⟨hm, ?_⟩) hmean
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m * H), div_le_one (by positivity),
    abs_mul, abs_two]
  linarith

/-- **Proposition `as:prop:window`, last sentence** (`d = 1`, `m = 3`). -/
theorem propWindowThree : PropWindowThree := by
  intro c H ν hH hν hsupp hmean
  refine inAgg_of_window_one (m := 3) hH (hsupp.mono fun t ht => Or.inr ⟨rfl, ?_⟩)
    (by rw [hmean]; norm_num)
  push_cast
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * H), div_le_iff₀ (by positivity),
    abs_mul, abs_two]
  linarith


/-! ### Products of kernels -/

lemma measurable_pi_measure {X ι : Type*} [MeasurableSpace X] [Fintype ι] {α : ι → Type*}
    [∀ q, MeasurableSpace (α q)] {f : ∀ q, X → Measure (α q)} (hf : ∀ q, Measurable (f q))
    (hp : ∀ q x, IsProbabilityMeasure (f q x)) :
    Measurable fun x => Measure.pi fun q => f q x := by
  refine Measure.measurable_of_measurable_coe _
    (MeasurableSpace.induction_on_inter generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_)
  · simp
  · rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ fun q _ =>
      (Measure.measurable_coe (hs q (Set.mem_univ q))).comp (hf q)
  · intro t ht ih
    have : (fun x => Measure.pi (fun q => f q x) tᶜ) =
        fun x => 1 - Measure.pi (fun q => f q x) t := by
      funext x; rw [prob_compl_eq_one_sub ht]
    rw [this]; exact measurable_const.sub ih
  · intro g hdisj hgm ih
    have : (fun x => Measure.pi (fun q => f q x) (⋃ i, g i)) =
        fun x => ∑' i, Measure.pi (fun q => f q x) (g i) := by
      funext x; rw [measure_iUnion hdisj hgm]
    rw [this]; exact Measurable.tsum ih

/-- Selecting one coordinate `y (i, k)` from each factor `k` of a product over pairs. -/
lemma pi_map_select {d : ℕ} {β : Type*} [MeasurableSpace β] (μ : Fin d × Fin d → Measure β)
    [∀ q, IsProbabilityMeasure (μ q)] (i : Fin d) (g : Fin d → β → ℝ)
    (hg : ∀ k, Measurable (g k)) :
    (Measure.pi μ).map (fun y k => g k (y (i, k))) =
      Measure.pi fun k => (μ (i, k)).map (g k) := by
  have hm : Measurable fun y : Fin d × Fin d → β => fun k => g k (y (i, k)) :=
    measurable_pi_iff.2 fun k => (hg k).comp (measurable_pi_apply _)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun y : Fin d × Fin d → β => fun k => g k (y (i, k))) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun q => if q.1 = i then g q.2 ⁻¹' s q.2 else Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h q; split_ifs with hq
      · obtain ⟨a, b⟩ := q; simp only at hq; subst hq; exact h b
      · trivial
    · intro h k; simpa using h (i, k)
  rw [hpre, Measure.pi_pi, Fintype.prod_prod_type]
  rw [Finset.prod_eq_single i]
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [if_true]
    rw [Measure.map_apply (hg k) (hs k)]
  · intro a _ ha
    simp [ha]
  · simp

/-- Averaging one factor of a product measure. -/
lemma bind_pi_update {X : Type*} [MeasurableSpace X] {d : ℕ} {ν : Measure X}
    [IsProbabilityMeasure ν] (i : Fin d) {f : X → Measure ℝ} (hf : Measurable f)
    (hfp : ∀ x, IsProbabilityMeasure (f x)) (ρ : Fin d → Measure ℝ)
    [∀ k, IsProbabilityMeasure (ρ k)] :
    ν.bind (fun x => Measure.pi fun k => if k = i then f x else ρ k) =
      Measure.pi fun k => if k = i then ν.bind f else ρ k := by
  have hb : IsProbabilityMeasure (ν.bind f) := ⟨by
    rw [Measure.bind_apply MeasurableSet.univ hf.aemeasurable]; simp⟩
  have hfk : ∀ k x, IsProbabilityMeasure (if k = i then f x else ρ k) := fun k x => by
    split_ifs <;> infer_instance
  have hk : ∀ k, IsProbabilityMeasure (if k = i then ν.bind f else ρ k) := fun k => by
    split_ifs <;> infer_instance
  have hmeas : Measurable fun x => Measure.pi fun k => if k = i then f x else ρ k := by
    refine measurable_pi_measure (fun k => ?_) hfk
    split_ifs
    · exact hf
    · exact measurable_const
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) hmeas.aemeasurable]
  simp only [Measure.pi_pi]
  have e : ∀ x, ∏ k, (if k = i then f x else ρ k) (s k) =
      f x (s i) * ∏ k ∈ Finset.univ.erase i, ρ k (s k) := by
    intro x
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [if_neg (Finset.ne_of_mem_erase hk)]
  simp only [e]
  have hmc : Measurable fun x => f x (s i) := (Measure.measurable_coe (hs i)).comp hf
  rw [lintegral_mul_const _ hmc,
    ← Measure.bind_apply (hs i) hf.aemeasurable, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [if_neg (Finset.ne_of_mem_erase hk)]

lemma map_eq_dirac' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → β} {c : β} (h : ∀ᵐ x ∂μ, f x = c) :
    μ.map f = Measure.dirac c := by
  rw [Measure.map_congr (g := fun _ => c) h, Measure.map_const, measure_univ, one_smul]

/-! ### The uniform distribution on a box -/

lemma unifI_apply' {l r : ℝ} (h : l < r) {s : Set ℝ} (hs : MeasurableSet s) :
    unifI l r s = (volume (Set.Icc l r))⁻¹ * volume (s ∩ Set.Icc l r) := by
  rw [unifI_of_lt h, smul_apply, Measure.restrict_apply hs, smul_eq_mul, Real.volume_Icc]

lemma unifSet_box {d : ℕ} (c H : Fin d → ℝ) (hH : ∀ i, 0 < H i) :
    unifSet (box c H) = Measure.pi fun i => unifI (c i - H i) (c i + H i) := by
  have hlt : ∀ i, c i - H i < c i + H i := fun i => by linarith [hH i]
  have h0 : ∀ i, volume (Set.Icc (c i - H i) (c i + H i)) ≠ 0 := fun i => by
    rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith [hH i]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [unifSet, box, smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi, volume_pi_pi, smul_eq_mul,
    Finset.prod_congr rfl fun i _ => unifI_apply' (hlt i) (hs i), Finset.prod_mul_distrib,
    ENNReal.prod_inv_distrib fun i _ j _ _ => Or.inl (h0 i)]

/-! ### Proposition `as:prop:window` in `ℝ^d` -/

/-- `γ` clamped into `[-1, 1]`. -/
def clamp1 (γ : ℝ) : ℝ := max (-1) (min γ 1)

lemma measurable_clamp1 : Measurable clamp1 := by unfold clamp1; fun_prop

lemma abs_clamp1_le (γ : ℝ) : |clamp1 γ| ≤ 1 := by
  unfold clamp1; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

lemma clamp1_eq {γ : ℝ} (h : |γ| ≤ 1) : clamp1 γ = γ := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  unfold clamp1; rw [min_eq_left h2, max_eq_right h1]


section Box

variable {d : ℕ}

/-- Extension of a finite tuple by zeros. -/
def extZ (n : ℕ) (x : Fin n → ℝ) : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else 0

lemma measurable_extZ (n : ℕ) : Measurable (extZ n) := by
  refine measurable_pi_iff.2 fun k => ?_
  unfold extZ
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-- The prescribed sum of the `i'`-th coordinates of the vectors of block `i`:
`mᵢ c_{i'}`, plus `t_i - m c_i` if `i' = i`. -/
def tgt (c : Fin d → ℝ) (mi : Fin d → ℕ) (q : Fin d × Fin d) (t : Fin d → ℝ) : ℝ :=
  mi q.1 * c q.2 + if q.1 = q.2 then t q.2 - (∑ k, mi k : ℕ) * c q.2 else 0

lemma measurable_tgt (c : Fin d → ℝ) (mi : Fin d → ℕ) (q : Fin d × Fin d) :
    Measurable (tgt c mi q) := by
  unfold tgt
  split_ifs
  · exact measurable_const.add ((measurable_pi_apply _).sub measurable_const)
  · exact measurable_const

/-- The factor for the pair `q = (block, coordinate)`: the window kernel in dimension one. -/
def facK (c H : Fin d → ℝ) (mi : Fin d → ℕ) (q : Fin d × Fin d) (t : Fin d → ℝ) :
    Measure (ℕ → ℝ) :=
  (winK (mi q.1) (c q.2) (H q.2) (tgt c mi q t)).map (extZ (mi q.1))

lemma measurable_facK (c H : Fin d → ℝ) (mi : Fin d → ℕ) (q : Fin d × Fin d) :
    Measurable (facK c H mi q) :=
  (Measure.measurable_map _ (measurable_extZ _)).comp
    ((measurable_winK _ _ _).comp (measurable_tgt c mi q))

lemma isProb_facK (c H : Fin d → ℝ) {mi : Fin d → ℕ} (hmi : ∀ i, 4 ≤ mi i) (q : Fin d × Fin d)
    (t : Fin d → ℝ) : IsProbabilityMeasure (facK c H mi q t) := by
  have := isProb_tiltK (by linarith [hmi q.1] : 3 ≤ mi q.1)
    (2 * (tgt c mi q t - (mi q.1 : ℝ) * c q.2) / ((mi q.1 : ℝ) * H q.2))
  unfold facK winK; infer_instance

/-- Assembling the vectors: vector `k ↔ (i, j)` has coordinates `y (i, i') j`. -/
def assemble (mi : Fin d → ℕ) (y : Fin d × Fin d → ℕ → ℝ) : Fin (∑ k, mi k) → Fin d → ℝ :=
  fun k i' => y ((finSigmaFinEquiv.symm k).1, i') (finSigmaFinEquiv.symm k).2

lemma measurable_assemble (mi : Fin d → ℕ) : Measurable (assemble mi) :=
  measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- The kernel of Proposition `as:prop:window`: given the sum `t`, independent factors for all
pairs (block, coordinate), assembled into `m` vectors. -/
def boxK (c H : Fin d → ℝ) (mi : Fin d → ℕ) (t : Fin d → ℝ) :
    Measure (Fin (∑ k, mi k) → Fin d → ℝ) :=
  (Measure.pi fun q => facK c H mi q t).map (assemble mi)

lemma measurable_boxK (c H : Fin d → ℝ) {mi : Fin d → ℕ} (hmi : ∀ i, 4 ≤ mi i) :
    Measurable (boxK c H mi) :=
  (Measure.measurable_map _ (measurable_assemble mi)).comp
    (measurable_pi_measure (measurable_facK c H mi) (isProb_facK c H hmi))

lemma tgt_gam (c H : Fin d → ℝ) (mi : Fin d → ℕ) (q : Fin d × Fin d) (t : Fin d → ℝ) :
    2 * (tgt c mi q t - (mi q.1 : ℝ) * c q.2) / ((mi q.1 : ℝ) * H q.2) =
      if q.1 = q.2 then 2 * (t q.2 - (∑ k, mi k : ℕ) * c q.2) / (mi q.1 * H q.2) else 0 := by
  unfold tgt; split_ifs <;> ring

theorem window_box (c H : Fin d → ℝ) (mi : Fin d → ℕ) (hH : ∀ i, 0 < H i)
    (hmi : ∀ i, 4 ≤ mi i) (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ x ∂ν, ∀ i, |x i - (∑ k, mi k : ℕ) * c i| ≤ mi i * H i / 2)
    (hmean : ∫ x, x ∂ν = ((∑ k, mi k : ℕ) : ℝ) • c) :
    IsProbabilityMeasure (ν.bind (boxK c H mi)) ∧
      (∀ k, (ν.bind (boxK c H mi)).map (fun x => x k) = unifSet (box c H)) ∧
      (ν.bind (boxK c H mi)).map (fun x => ∑ k, x k) = ν := by
  set m : ℕ := ∑ k, mi k with hm_def
  have hbk := measurable_boxK c H hmi
  have hfp := isProb_facK c H hmi
  have hbp : ∀ t, IsProbabilityMeasure (boxK c H mi t) := fun t => by
    unfold boxK; infer_instance
  have hmi' : ∀ i, (0 : ℝ) < mi i := fun i => by exact_mod_cast (by linarith [hmi i] : 0 < mi i)
  -- the tilt parameter of block `i`
  set g : Fin d → (Fin d → ℝ) → ℝ := fun i t => 2 * (t i - (m : ℝ) * c i) / (mi i * H i)
    with hg_def
  have hgm : ∀ i, Measurable (g i) := fun i => by
    simp only [hg_def]; exact (((measurable_pi_apply i).sub measurable_const).const_mul _).div_const _
  have hgb : ∀ᵐ t ∂ν, ∀ i, |g i t| ≤ 1 := hsupp.mono fun t ht i => by
    simp only [hg_def]
    rw [abs_div, abs_of_pos (mul_pos (hmi' i) (hH i)), div_le_one (mul_pos (hmi' i) (hH i)),
      abs_mul, abs_two]
    linarith [ht i]
  have hrange : ∀ᵐ t ∂ν, ∀ q : Fin d × Fin d,
      TiltRange (mi q.1) (2 * (tgt c mi q t - (mi q.1 : ℝ) * c q.2) / ((mi q.1 : ℝ) * H q.2)) := by
    filter_upwards [hgb] with t ht q
    refine Or.inl ⟨hmi q.1, ?_⟩
    rw [tgt_gam]
    split_ifs with hq
    · have := ht q.2; simp only [hg_def] at this; rwa [hq]
    · simp
  refine ⟨⟨?_⟩, fun k => ?_, ?_⟩
  · rw [Measure.bind_apply MeasurableSet.univ hbk.aemeasurable]; simp
  · -- marginals
    set s := (finSigmaFinEquiv.symm k : (i : Fin d) × Fin (mi i)) with hs_def
    set aff : ℝ → ℝ := fun z => H s.1 * z + c s.1 with haff
    have haffm : Measurable aff := by simp only [haff]; fun_prop
    set f : (Fin d → ℝ) → Measure ℝ := fun t => (tiltLin 1 (clamp1 (g s.1 t))).map aff
      with hf_def
    have hfm : Measurable f := (Measure.measurable_map _ haffm).comp
      ((measurable_tiltLin 1).comp (measurable_clamp1.comp (hgm s.1)))
    have hfp' : ∀ t, IsProbabilityMeasure (f t) := fun t => by
      have := isProb_tilt one_pos (abs_clamp1_le (g s.1 t))
      simp only [hf_def]; rw [← tilt_eq_tiltLin one_pos (abs_clamp1_le _)]; infer_instance
    rw [Measure.map_bind hbk.aemeasurable (measurable_pi_apply k).aemeasurable]
    have h1 : (fun t => (boxK c H mi t).map (fun x => x k)) =ᵐ[ν] fun t => Measure.pi
        (fun i' => if i' = s.1 then f t else unifI (c i' - H i') (c i' + H i')) := by
      filter_upwards [hrange, hgb] with t hr hb
      rw [boxK, Measure.map_map (measurable_pi_apply k) (measurable_assemble mi)]
      rw [show (fun x : Fin (∑ k, mi k) → Fin d → ℝ => x k) ∘ assemble mi =
        fun y i' => y (s.1, i') s.2 from rfl]
      have hsel := pi_map_select (fun q => facK c H mi q t) s.1 (fun _ z => z s.2)
        (fun _ => measurable_pi_apply _)
      rw [hsel]
      congr 1; funext i'
      rw [facK, Measure.map_map (measurable_pi_apply _) (measurable_extZ _)]
      have e : (fun z : ℕ → ℝ => z s.2) ∘ extZ (mi s.1) = fun x => x s.2 := by
        funext x; simp [extZ]
      rw [e, (winK_spec (hH i') (hr (s.1, i'))).1.2.2 s.2, tgt_gam]
      simp only
      split_ifs with h2 h3 h3
      · subst h2
        simp only [hf_def, haff]
        rw [clamp1_eq (hb s.1), tilt_eq one_pos (hb s.1)]
        rfl
      · exact absurd h2.symm h3
      · exact absurd h3.symm h2
      · rw [tilt_eq one_pos (by simp)]
        exact tiltLin_zero_map (hH i')
    have hint : Integrable (fun x : Fin d → ℝ => x) ν := by
      set C : ℝ := ∑ i, (|(m : ℝ) * c i| + mi i * H i / 2) with hC
      have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (by have := hH i; have := hmi' i; positivity)
      refine (integrable_const C).mono' measurable_id.aestronglyMeasurable ?_
      filter_upwards [hsupp] with x hx
      rw [pi_norm_le_iff_of_nonneg hC0]
      intro i
      have h1 := hx i
      have h2 : |(m : ℝ) * c i| + mi i * H i / 2 ≤ C :=
        Finset.single_le_sum (f := fun i => |(m : ℝ) * c i| + mi i * H i / 2)
          (fun i _ => add_nonneg (abs_nonneg _) (by have := hH i; have := hmi' i; positivity))
          (Finset.mem_univ i)
      rw [Real.norm_eq_abs]
      calc |x i| = |(x i - m * c i) + m * c i| := by ring_nf
        _ ≤ |x i - m * c i| + |(m : ℝ) * c i| := abs_add_le _ _
        _ ≤ C := by linarith
    have hci : ∫ x, x s.1 ∂ν = m * c s.1 := by
      have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) s.1).integral_comp_comm
        hint
      simp only [ContinuousLinearMap.proj_apply] at this
      rw [this, hmean]; simp
    have hg0 : ∫ t, clamp1 (g s.1 t) ∂ν = 0 := by
      rw [integral_congr_ae (hgb.mono fun t ht => clamp1_eq (ht s.1))]
      simp only [hg_def]
      have hi1 : Integrable (fun x : Fin d → ℝ => x s.1) ν :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) s.1).integrable_comp hint
      rw [integral_div, integral_const_mul, integral_sub hi1 (integrable_const _), hci,
        integral_const]
      simp
    rw [bind_congr_ae h1, bind_pi_update s.1 hfm hfp', unifSet_box c H hH]
    have hbf : ν.bind f = unifI (c s.1 - H s.1) (c s.1 + H s.1) := by
      have hm2 : Measurable fun t => tiltLin 1 (clamp1 (g s.1 t)) :=
        (measurable_tiltLin 1).comp (measurable_clamp1.comp (hgm s.1))
      simp only [hf_def]
      have hcm : Measurable fun t => clamp1 (g s.1 t) := measurable_clamp1.comp (hgm s.1)
      rw [← Measure.map_bind hm2.aemeasurable haffm.aemeasurable,
        bind_tiltLin 1 hcm
          (Filter.Eventually.of_forall fun t => abs_clamp1_le _), hg0]
      exact tiltLin_zero_map (hH s.1)
    rw [hbf]
    congr 1; funext i'
    split_ifs with h
    · subst h; rfl
    · rfl
  · -- the sum
    have hsm : Measurable fun x : Fin (∑ k, mi k) → Fin d → ℝ => ∑ k, x k :=
      Finset.measurable_sum _ fun k _ => measurable_pi_apply k
    rw [Measure.map_bind hbk.aemeasurable hsm.aemeasurable]
    have h2 : (fun t => (boxK c H mi t).map (fun x => ∑ k, x k)) =ᵐ[ν] Measure.dirac := by
      filter_upwards [hrange] with t hr
      rw [boxK, Measure.map_map hsm (measurable_assemble mi)]
      refine map_eq_dirac' ?_
      have hq : ∀ q : Fin d × Fin d, ∀ᵐ y ∂(Measure.pi fun q => facK c H mi q t),
          ∑ n : Fin (mi q.1), y q n = tgt c mi q t := by
        intro q
        have h3 : ∀ᵐ z ∂(facK c H mi q t), ∑ n : Fin (mi q.1), z n = tgt c mi q t := by
          have hms : MeasurableSet {z : ℕ → ℝ | ∑ n : Fin (mi q.1), z n = tgt c mi q t} :=
            measurableSet_eq_fun (Finset.measurable_sum Finset.univ
              fun (n : Fin (mi q.1)) _ => measurable_pi_apply (n : ℕ)) measurable_const
          rw [facK, ae_map_iff (measurable_extZ _).aemeasurable hms]
          filter_upwards [(winK_spec (hH q.2) (hr q)).2] with x hx
          rw [← hx]
          exact Finset.sum_congr rfl fun n _ => by simp [extZ]
        exact (Measure.tendsto_eval_ae_ae (μ := fun q => facK c H mi q t) (i := q)).eventually h3
      filter_upwards [ae_all_iff.2 hq] with y hy
      funext i'
      simp only [Function.comp, assemble, Finset.sum_apply]
      rw [Equiv.sum_comp finSigmaFinEquiv.symm
        (fun s : (i : Fin d) × Fin (mi i) => y (s.1, i') s.2), Fintype.sum_sigma]
      have hy' : ∀ i, ∑ j : Fin (mi i), y (i, i') j = tgt c mi (i, i') t := fun i => hy (i, i')
      simp only [hy', tgt]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i', if_pos (Finset.mem_univ _),
        ← Finset.sum_mul]
      push_cast; ring
    rw [bind_congr_ae h2, Measure.bind_dirac]

/-- **Proposition `as:prop:window`**. -/
theorem propWindow : PropWindow := by
  intro d c H mi ν hH hmi hν hsupp hmean
  obtain ⟨h1, h2, h3⟩ := window_box c H mi hH hmi ν hsupp hmean
  exact ⟨_, h1, h2, h3⟩

end Box

end AsymWindow

end Mixes
