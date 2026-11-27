import Mixes.Theorem27
import Mixes.ClassK
import Mixes.BallBridge

/-!
# Results with Theorem 27 discharged

`Theorem27.lean` proves Theorem 27 and its consequences `Thm27Frustum m q` (`0 ≤ q < 1`) and
Corollary 30 (`cor30`). This file removes the hypothesis from Corollary 58 (truncated pyramids and
frusta over balls) and Theorem 61 (the class `K`). Corollary 64 takes `Theorem27.cor30 n` for its
hypothesis `Cor30 n`, and Corollaries 44, 45 are stated unconditionally in `Theorem27.lean`.
-/

open MeasureTheory

noncomputable section

namespace Mixes.Unconditional

open FrustumMix in
/-- **Corollary 58**, truncated pyramids over cubes, without hypotheses. -/
theorem pyramid_completelyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {n : ℕ}
    (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (frustumSet q (cubeSet (m' + 1)))) ↔ aKQ (m' + 2) q ≤ n :=
  FrustumMix.pyramid_completelyMixable_iff hq0 hq1 (Theorem27.thm27Frustum _ hq0 hq1)
    (ConeMix.scalingProperty_cube _) hn

open FrustumMix in
/-- **Corollary 58**, frusta over balls, without hypotheses. -/
theorem circCone_completelyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {n : ℕ}
    (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (frustumSet q (ballSet (m' + 1)))) ↔ aKQ (m' + 2) q ≤ n :=
  BallBridge.circCone_completelyMixable_iff hq0 hq1 (Theorem27.thm27Frustum _ hq0 hq1) hn

open ClassK

/-- **Theorem 61**, scaling property, without hypotheses. -/
theorem classK_scalingProperty {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) :
    ScalingPropertySet K ((d : ℝ) + 1) :=
  classK_scalingProperty' Theorem27.thm27Frustum_all hK

/-- **Theorem 61**, joint mixes, without hypotheses. -/
theorem classK_jointlyMixable {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ}
    (lam : Fin n → ℝ) (t : Fin n → Fin d → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hne : ∃ i, lam i ≠ 0)
    (hc : ∀ k, ((d : ℝ) + 1) * lam k ≤ ∑ i, lam i) :
    JointlyMixable fun i => unifScaled K (t i) (lam i) :=
  classK_jointlyMixable' Theorem27.thm27Frustum_all hK lam t hlam hne hc

/-- **Theorem 61**, complete mixes, without hypotheses. -/
theorem classK_completelyMixable {d : ℕ} {K : Set (Fin d → ℝ)} (hK : InK d K) {n : ℕ}
    (hn : d + 1 ≤ n) : CompletelyMixable n (unifSet K) :=
  classK_completelyMixable' Theorem27.thm27Frustum_all hK hn

/-- **Theorem 61**, cones over members of the class, without hypotheses. -/
theorem cone_completelyMixable_iff {m : ℕ} {B : Set (Fin m → ℝ)} (hB : InK m B)
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] ℝ × (Fin m → ℝ)) {n : ℕ} (hn : 1 ≤ n) :
    CompletelyMixable n (unifSet (coneSet L B)) ↔ m + 1 + 1 ≤ n :=
  cone_completelyMixable_iff' Theorem27.thm27Frustum_all hB L hn

end Mixes.Unconditional
