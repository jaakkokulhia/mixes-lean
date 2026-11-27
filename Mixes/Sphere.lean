import Mixes.Ball

/-!
# Uniqueness of the rotation-invariant probability measure on the sphere

This file proves `Mixes.Ball.SphereUniqueness E` for every finite-dimensional real inner product
space `E` (every dimension; in dimension `0` the statement is vacuous, in dimension `1` the sphere
is `{±1}`), and restates Lemma 50 and Proposition 52 of `Ball.lean` without that hypothesis.

Proof (no Haar measure): the characteristic function `φ_μ` of a rotation-invariant measure `μ` is
constant on spheres, because the orthogonal group acts transitively on each sphere (a reflection
maps `t` to any vector of the same norm, `reflection_sub`). Hence, for invariant probabilities
`μ, ν` carried by the unit sphere,
`φ_μ(t) = ∫ φ_μ(‖t‖ u) dν(u) = ∫∫ e^{i ‖t‖ ⟪x, u⟫} dμ(x) dν(u) = ∫ φ_ν(‖t‖ x) dμ(x) = φ_ν(t)`
(Fubini), and `μ = ν` by `Measure.ext_of_charFun`.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace Mixes

namespace Sphere

open Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The characteristic function of a rotation-invariant measure is rotation invariant. -/
lemma charFun_iso {μ : Measure E} (hμ : IsRotInv μ) (L : E ≃ₗᵢ[ℝ] E) (t : E) :
    charFun μ (L t) = charFun μ t := by
  conv_lhs => rw [← hμ L]
  rw [charFun_apply, charFun_apply, integral_map L.continuous.aemeasurable (by fun_prop)]
  simp

/-- The orthogonal group acts transitively on spheres: `φ_μ (‖t‖ u) = φ_μ t` for `‖u‖ = 1`. -/
lemma charFun_norm_smul {μ : Measure E} (hμ : IsRotInv μ) (t : E) {u : E} (hu : ‖u‖ = 1) :
    charFun μ (‖t‖ • u) = charFun μ t := by
  have h : ‖t‖ = ‖‖t‖ • u‖ := by rw [norm_smul, hu, norm_norm, mul_one]
  rw [← Submodule.reflection_sub h, charFun_iso hμ]

/-- The key identity `φ_μ t = ∫ φ_ν (‖t‖ x) dμ(x)` for invariant `μ` and `ν` carried by the unit
sphere. -/
lemma charFun_eq_integral {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν (Metric.sphere 0 1)ᶜ = 0) (hμ : IsRotInv μ) (t : E) :
    charFun μ t = ∫ x, charFun ν (‖t‖ • x) ∂μ := by
  have hae : ∀ᵐ u ∂ν, charFun μ (‖t‖ • u) = charFun μ t := by
    rw [ae_iff]
    refine measure_mono_null (fun u hu => ?_) hν
    intro hs
    exact hu (charFun_norm_smul hμ t (mem_sphere_zero_iff_norm.1 hs))
  have h1 : charFun μ t = ∫ u, charFun μ (‖t‖ • u) ∂ν := by
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
  rw [h1]
  simp only [charFun_apply]
  have hint : Integrable (Function.uncurry fun (u x : E) => exp (⟪x, ‖t‖ • u⟫_ℝ * I))
      (ν.prod μ) := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun z => ?_)
    simp [Function.uncurry, norm_exp_ofReal_mul_I]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [real_inner_smul_right, real_inner_comm]

/-- **Uniqueness of the uniform distribution on the sphere**: two probability measures carried by
the unit sphere of a finite-dimensional real inner product space and invariant under the
orthogonal group are equal. This is the hypothesis `Ball.SphereUniqueness E`, in every
dimension. -/
theorem sphereUniqueness : SphereUniqueness E := by
  intro μ ν _ _ hμs hνs hμ hν
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_eq_integral hνs hμ t]
  have hae : ∀ᵐ x ∂μ, charFun ν (‖t‖ • x) = charFun ν t := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hμs
    intro hs
    exact hx (charFun_norm_smul hν t (mem_sphere_zero_iff_norm.1 hs))
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-! ### Unconditional versions of the results of `Ball.lean` that assumed the uniqueness -/

/-- **Polar decomposition** (unconditional `Ball.polar_of_unique`): a rotation-invariant
probability measure `P` is the law of `R Θ` with `R ∼ ‖X‖`, `X ∼ P`, and `Θ ∼ σ` independent,
for any rotation-invariant probability measure `σ` carried by the unit sphere. -/
theorem polar {σ : Measure E} [IsProbabilityMeasure σ] (hσs : σ (Metric.sphere 0 1)ᶜ = 0)
    (hσ : IsRotInv σ) {P : Measure E} [IsProbabilityMeasure P] (hP : IsRotInv P) :
    P = ((P.map norm).prod σ).map (fun z => z.1 • z.2) :=
  polar_of_unique sphereUniqueness hσs hσ hP

/-- **Lemma 50** (`b:lem:frame`), unconditional: for `j ≥ 2` and `a² + b² = 1`, the vector
`a g₁ + b g₂` built from two independent standard Gaussian vectors (the Gaussian frame) has the
law of `g₁ = Z₁/|Z₁|`, the uniform distribution on the sphere. -/
theorem lemma50 (hE : 2 ≤ Module.finrank ℝ E) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    (gauss2 E).map (fun z => a • frame1 z + b • frame2 z) = sphUnif E :=
  Ball.lemma50 sphereUniqueness hE hab

/-- Lemma 50 scaled, unconditional: if `a² + b² = s²` with `s ≥ 0`, then `a g₁ + b g₂ ∼ s Θ`,
`Θ ∼ sphUnif`. -/
theorem frame_law_scaled (hE : 2 ≤ Module.finrank ℝ E) {a b s : ℝ} (hs : 0 ≤ s)
    (h : a ^ 2 + b ^ 2 = s ^ 2) :
    (gauss2 E).map (fun z => a • frame1 z + b • frame2 z) = (sphUnif E).map (fun θ => s • θ) :=
  Ball.frame_law_scaled sphereUniqueness hE hs h

/-- **Proposition 52** (`b:prop:radial`), sufficiency, unconditional: let `j ≥ 2`, let
`P_1, …, P_n` be rotation-invariant probability measures, and let `Q` be a coupling of their
radial distributions with `2 max R ≤ ∑ R` almost surely. Then the law of
`X_i = v_{i1} g₁ + v_{i2} g₂` (polygon of Lemma 49 for the lengths `R`, Gaussian frame
independent of `R`) is a joint mix of the `P_i` with sum `0`. -/
theorem prop52_sufficiency (hE : 2 ≤ Module.finrank ℝ E) {n : ℕ}
    (P : Fin n → Measure E) [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, IsRotInv (P i))
    (Q : Measure (Fin n → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ i, Q.map (fun r => r i) = (P i).map norm)
    (hpoly : ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l) :
    IsJointMix P ((Q.prod (gauss2 E)).map (radialMix n)) ∧
      ∀ᵐ x ∂((Q.prod (gauss2 E)).map (radialMix n)), ∑ i, x i = 0 :=
  Ball.prop52_sufficiency sphereUniqueness hE P hP Q hQ hpoly

/-- **Proposition 52** (`b:prop:radial`), unconditional: for `j ≥ 2`, rotation-invariant
distributions with finite means are jointly mixable if and only if their radial distributions
have a coupling `R` with `2 max R ≤ ∑ R` almost surely. -/
theorem prop52 (hE : 2 ≤ Module.finrank ℝ E) {n : ℕ}
    (P : Fin n → Measure E) [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, IsRotInv (P i))
    (hint : ∀ i, Integrable id (P i)) :
    JointlyMixable P ↔ ∃ Q : Measure (Fin n → ℝ), IsProbabilityMeasure Q ∧
      (∀ i, Q.map (fun r => r i) = (P i).map norm) ∧ ∀ᵐ r ∂Q, ∀ i, 2 * r i ≤ ∑ l, r l :=
  Ball.prop52 sphereUniqueness hE P hP hint

/-- Last claim of Proposition 52, unconditional: a rotation-invariant distribution on `ℝ^j`,
`j ≥ 2`, is `n`-completely mixable for every `n ≥ 2` (no finite mean needed). -/
theorem completelyMixable_of_isRotInv (hE : 2 ≤ Module.finrank ℝ E) {P : Measure E}
    [IsProbabilityMeasure P] (hP : IsRotInv P) {n : ℕ} (hn : 2 ≤ n) :
    CompletelyMixable n P :=
  Ball.completelyMixable_of_isRotInv sphereUniqueness hE hP hn

end Sphere

end Mixes
