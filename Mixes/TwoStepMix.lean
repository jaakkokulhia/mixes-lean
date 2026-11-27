import Mixes.TwoStep
import Mixes.Uniform

/-!
# Theorem 6 and Corollary 7 without hypotheses

`TwoStep.lean` proves the complete mixability of `g_{a,b}` granted Lemma 3 in list form
(`Mixes.TwoStep.Lemma3`). `Uniform.lean` proves Lemma 3 (with Lemma 1 and the theorem of
Archimedes) for finitely indexed mixtures. This file discharges the hypothesis.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Mixes

/-- **Lemma 3** in the list form used by `TwoStep.lean`. -/
theorem lemma3_list (n : ℕ) : TwoStep.Lemma3 n := by
  intro L hL
  have hw : ∑ i : Fin L.length, (L.get i).1 = 1 := by
    rw [← hL, ← List.sum_ofFn, List.ofFn_comp' L.get Prod.fst, List.ofFn_get]
  obtain ⟨Q, hQ, -⟩ :=
    completelyMixable_mixtureMarginal' (fun i : Fin L.length => (L.get i).1) hw
      (fun i => (L.get i).2)
  refine ⟨Q, ?_⟩
  have : mixtureMarginal (fun i : Fin L.length => (L.get i).1) (fun i => (L.get i).2) =
      (L.map fun q => q.1 • q.2.marginal).sum := by
    unfold mixtureMarginal
    rw [← List.sum_ofFn, List.ofFn_comp' L.get (fun q => q.1 • q.2.marginal), List.ofFn_get]
  exact this ▸ hQ

/-- **Theorem 6, final sentence**, unconditional: for `n ≥ 3` and `0 < a < 2 < b ≤ n`, the
distribution with density `g_{a,b}` is `n`-completely mixable. -/
theorem completelyMixable_g {n : ℕ} {a b : ℝ} (hn : 3 ≤ n) (ha0 : 0 < a) (ha2 : a < 2)
    (hb2 : 2 < b) (hbn : b ≤ n) :
    CompletelyMixable n (volume.withDensity (fun x => ENNReal.ofReal (TwoStep.g a b x))) :=
  TwoStep.completelyMixable_g (lemma3_list n) hn ha0 ha2 hb2 hbn

end Mixes
