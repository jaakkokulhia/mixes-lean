import Mixes.Ball
import Mixes.FrustumMix
import Mixes.SymmCor

/-!
# Discharging the ball hypotheses

`Ball.lean` proves the sufficiency in Theorem 51 (`ball_scalingProperty`,
`ball_completelyMixable`). This file removes the hypothesis `hball` from the results of
`FrustumMix.lean` (frusta over balls, Corollary 58) and `SymmCor.lean` (Corollary 99(a)).
-/

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

namespace Mixes.BallBridge

/-- Corollary 58 for frusta over balls, with the scaling property of the ball proved. -/
theorem circCone_completelyMixable_iff {m' : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h27 : FrustumMix.Thm27Frustum (m' + 1) q) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n (unifSet (FrustumMix.frustumSet q (FrustumMix.ballSet (m' + 1)))) ↔
      Mixes.aKQ (m' + 2) q ≤ n :=
  FrustumMix.circCone_completelyMixable_iff hq0 hq1 h27 (Ball.ball_scalingProperty (m' + 1)) hn

/-- Corollary 99(a) in the plane, with Theorem 51 proved. -/
theorem partA_plane {K : Set (EuclideanSpace ℝ (Fin 2))} {c : EuclideanSpace ℝ (Fin 2)}
    (hK : MeasurableSet K) (hKfin : volume K ≠ ∞) (hconv : Convex ℝ K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : EuclideanSpace ℝ (Fin 2))
      (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)),
      LinearMap.det T ≠ 0 ∧ SymmCor.ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ 2 / (volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal *
        (volume (SymmCor.ell e T)).toReal) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → CompletelyMixable n (unifSet K) :=
  SymmCor.partA_plane hK hKfin hconv hKs hJB (Ball.ball_completelyMixable 2 (by norm_num))

/-- Corollary 99(a) in space, with Theorem 51 proved. -/
theorem partA_space {K : Set (EuclideanSpace ℝ (Fin 3))} {c : EuclideanSpace ℝ (Fin 3)}
    (hK : MeasurableSet K) (hKfin : volume K ≠ ∞) (hconv : Convex ℝ K)
    (hKs : AffineEquiv.pointReflection ℝ c '' K = K)
    (hJB : ∃ (e : EuclideanSpace ℝ (Fin 3))
      (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)),
      LinearMap.det T ≠ 0 ∧ SymmCor.ell e T ⊆ K ∧
      (volume K).toReal ≤ 2 ^ 3 / (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal *
        (volume (SymmCor.ell e T)).toReal) :
    ∀ n : ℕ, 2 ≤ n → n ≠ 3 → n ≠ 5 → CompletelyMixable n (unifSet K) :=
  SymmCor.partA_space hK hKfin hconv hKs hJB (Ball.ball_completelyMixable 3 (by norm_num))

end Mixes.BallBridge
