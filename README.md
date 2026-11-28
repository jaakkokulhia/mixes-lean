# Explicit complete and joint mixes, formalised in Lean 4

Lean 4 / Mathlib proofs of the results of the paper *Explicit Complete and Joint Mixes for
Monotone, Concave and Unimodal Densities, with Convex Bodies*, including every result used to
answer the open questions of Wang (2015). The results, the cited theorems that enter as explicit
hypotheses, and every difference between the formal statements and the paper are listed below.

## The setting

A joint mix of distributions `F_1, …, F_n` on a space `E` is a probability measure `P` on
`Fin n → E` whose coordinates have the laws `F_j` and whose coordinate sum is almost surely
constant (`IsJointMix`); an `n`-complete mix of `F` is a joint mix of `n` copies of `F`
(`IsCompleteMix`, `CompletelyMixable`). Random vectors are replaced by their laws throughout.
`unifI l r` is `U[l, r]` (the point mass at `l` when `l = r`), `unifSet K` is `U(K)`, and
`Admissible n` is Definition 2 (lengths with the polygon inequality, midpoints summing to `n`),
with marginal `n⁻¹ Σ_j U[l_j, r_j]`. All of this is in `Mixes/Defs.lean`.

## The results

- **Lemma 1, Definition 2, Lemma 3** (`Uniform.lean`): `lem_arch` (the joint mix of uniform
  distributions on intervals with the polygon inequality, from the balancing step, the triangle
  and the projection property of Archimedes), `lem_sym` (mixing and a uniformly random
  permutation give a complete mix) and `completelyMixable_mixtureMarginal'` (every finite mixture
  of admissible tuples has an `n`-complete mix of its marginal with sum `n`). No hypotheses.
- **Theorem 6, Lemmas 4, 5, Corollary 7** (`TwoStep.lean`, `TwoStepMix.lean`): the explicit
  mixtures of admissible tuples in cases (A) to (D) and for `1 < a < 2` (`thm6_i`, `thm6_ii`,
  `thm6_measure`), Corollary 7 (`cor7`), and `completelyMixable_g`: the two-step density
  `g_{a,b}` is `n`-completely mixable for `n ≥ 3`, `0 < a < 2 < b ≤ n`.
- **Lemmas 9, 10, Theorem 12, Corollary 13** (`Slabs.lean`, `SlabsMix.lean`): the slab lemma
  (`slab_lemma`), the pairs lemma (`pairs_lemma`), Algorithm 11 and Theorem 12 (`mono_mix`,
  `mono_completelyMixable`: a non-increasing density with mean 1 vanishing on `[B, ∞)`, `B ≤ n`, is
  `n`-completely mixable), and Corollary 13 (`cor13_nonincreasing`, `cor13_nondecreasing`). The
  mixes of Theorem 6 are assembled into a measurable kernel in `(a, b)` (`kappa_spec`), so no
  hypotheses remain.
- **Lemmas 16, 17, 18 and Proposition 24** (`Joint.lean`): mixtures of segments in the
  hyperplane (`seg_mix`, `seg_mix_density`), the three-segment joint mixes of uniform
  distributions (`lem17`, `lem18`), and the explicit joint mix of `U[0,c₁]`, `U[0,c₂]` and the
  two-step law `g^μ_{a,b}` in all five cases of the table (`prop24`, with `P24.cases_exclusive`).
  Theorem 27 is in `Theorem27.lean`.
- **Lemma 25 and Proposition 26** (`JointSplit.lean`): the grouping procedure terminates with two
  groups or three groups any two of which exceed `s` (`lem25`, `three_groups_bound`), and the
  splitting construction: the admissible `κ` (`prop26_kappa`), the laws `L_i` (`prop26_i`), the
  joint mix of the reflected laws (`prop26_ii`), and the joint mix of `U[0,C₁], U[0,C₂], U[0,C₃]`
  and `g^μ_{a,b}` on segments of the hyperplane (`prop26_iii`, `prop26`).
- **Lemmas 20 to 23** (`JointLemmas.lean`): the slab lemma for the class `D(B)` (`slab_lemma`,
  `slab_lemma_exists`), the recognition of `g^μ_{a,b}` (`recog_pos`, `recog_zero`), the pairs
  lemma (`pairs_lemma`, `pairs_lemma_F`) and the splitting procedure (`split_lemma`).
- **Proposition 32 and Lemma 38** (`Pieces.lean`): `pieces_mixture` (two admissible tuples whose
  mixture has marginal `P_β`, for `3 ≤ n`, `2 ≤ β ≤ n`) and `mean_mem_middle_third`.
- **Theorem 40, the inequalities** (`Trapezoid.lean`): `trap_polygon`, `trap_meancond`,
  `trap_const_sum`, and `trap_nh_eq_two_iff` (equality exactly when `q = 0` and `n = 3`).
- **Lemma 42, Theorem 43(a), Remark 47** (`Cone.lean`): the slicing of a cone
  (`unifSet_scaledCone`, `unifSet_scaledCone_split`, `unifSet_scaledCone_ae_reconstruct`), the
  necessity `(k+1)·max λ_i ≤ Σ λ_i` (`cone_jointlyMixable_le`), `n ≥ k + 1` for cones, simplices and
  pyramids over cubes (`cone_completelyMixable_le`, `simplex_completelyMixable_le`,
  `pyramid_completelyMixable_le`), and 2-complete mixability as central symmetry
  (`completelyMixable_two_iff`), with the trapezoid case (`trap_completelyMixable_two_iff`).
- **Theorem 43(b), Corollaries 44, 45, Remark 46** (`ConeMix.lean`): the sufficiency for cones
  (`cone_sufficiency`, `cone_scalingProperty`); every simplex of a `k`-dimensional space is
  `n`-completely mixable exactly when `n ≥ k + 1` (`simplex_completelyMixable_iff`), and every
  pyramid over a parallelotope exactly when `n ≥ d + 1` (`pyramid_completelyMixable_iff`), with
  Theorem 27 for the laws `G_{k,λ}` as the hypothesis `Thm27Frustum`; the necessity directions
  are unconditional. The scaling property of segments and cubes with constant 2 is proved
  (`scalingProperty_Icc`, `scalingProperty_cube`), and Remark 46 without hypotheses: every
  tetrahedron is `n`-completely mixable for `n ≥ 4` (`tetrahedron_completelyMixable`).
- **Theorem 40** (`Assembly.lean`): `completelyMixable_trapezoid'`: for `n ≥ 3` the uniform
  distribution on every trapezoid and every triangle is `n`-completely mixable. The proof
  disintegrates `U(T)` into the abscissa and the chords (`unifSet_trapSet_eq`), takes the abscissa
  mix from Corollary 13 (`completelyMixable_trapAbsc`) and Lemma 1 for the chords, with the
  choices made measurably (`chordVec_spec`), and reduces every trapezoid to the normal form by an
  affine map.
- **Lemmas 48, 53 and the necessity in Theorem 51** (`Bodies.lean`): the scaling property under
  affine maps (`scalingPropertySet_image_affine`) and products (`scalingPropertySet_prod`),
  `completelyMixable_prod_iff`, and `ball_necessity` (`2λ_k ≤ Σ λ_i` for jointly mixable balls).
- **Theorem 51, Lemma 50, Proposition 52** (`Ball.lean`, `BallBridge.lean`, `Sphere.lean`): Theorem 51 in every
  dimension without hypotheses (`ball_scalingProperty`: the ball has the scaling property with
  constant 2; `ball_jointlyMixable_iff`; `ball_completelyMixable`), which removes the ball
  hypothesis from Corollary 58 for frusta over balls and from Corollary 99(a)
  (`BallBridge.circCone_completelyMixable_iff`, `BallBridge.partA_plane`,
  `BallBridge.partA_space`); the necessity in Proposition 52 (`prop52_necessity`); Lemma 50
  and Proposition 52 (`Sphere.lemma50`, `Sphere.prop52`, `Sphere.completelyMixable_of_isRotInv`)
  without hypotheses: `Sphere.sphereUniqueness` proves that a probability measure on the sphere
  invariant under all linear isometries is unique, by characteristic functions and Fubini
  (`Ball.lean` states these results with that uniqueness as the hypothesis `SphereUniqueness`).
- **Lemma 59, Definition 60, Theorem 61** (`ClassK.lean`): joins of bodies with the scaling
  property (`unifSet_joinSet`, `join_scalingProperty`), the class `K` closed under affine maps,
  products and joins, and Theorem 61: every body of class `K` of dimension `k` has the scaling
  property and is `n`-completely mixable for `n ≥ k + 1` (`classK_scalingProperty'`,
  `classK_jointlyMixable'`, `classK_completelyMixable'`, `cone_completelyMixable_iff'`), with
  Theorem 27 for the laws `G_{k,λ}` as the hypothesis `Thm27Frustum`. The ball case is
  discharged from `Ball.lean` (`thm51Ball`). Lemma 59 is proved with its hypothesis
  `max(m₁, m₂) ≥ 1`, which cannot be dropped (`join_points_not_scaling`).
- **Remark 85, Lemmas 101, 102, 111, Propositions 106, 116, Corollaries 105, 114, 115**
  (`Large.lean`): Remark 85 (Minkowski–Radon, `asymLE_cent`, `centroid_support`,
  `neg_sub_cent_mem`) without hypotheses; Lemma 111(a), (b), (c) (`lemma111a`, `lemma111b`,
  `lemma111c`); Lemmas 101, 102; Proposition 106 (`prop106`) and the uniqueness of its density
  up to an exponential-affine factor (`prop106_unique`, from the kernel argument of Theorem 91 as
  the hypothesis `KernelAffine`); Proposition 116 (`prop116`, the conditioned product is the
  unique entropy maximiser). Corollary 115 (`cor115`) assumes Theorem 113 (`Thm113`);
  Corollary 114 (`cor114`) assumes John's theorem and Theorem 113 with one common correction
  (`Thm113Sym`); Corollary 105 (`cor105`: for every `d` there is `N_d` such that the uniform
  distribution on every convex body of `ℝ^d` is `n`-completely mixable for `n ≥ N_d`) assumes
  John's theorem, Theorem 104 with its constants tracked (`Thm104T`) and the uniform Fourier
  bound for bodies between `B` and `dB` (`FourierGapJohn`). Lemmas 103, 112 and Theorems 104,
  113 are not formalised.
- **Lemma 33, Theorems 34, 35, 36, Corollary 39** (`Peel.lean`, `Decomp.lean`,
  `ConcaveMix.lean`): Lemma 33 (`lemma33_continuousOn`, `lemma33_deriv_x`, `lemma33_deriv_U`,
  `lemma33_differentiable`, `lemma33_shape`); Theorem 34 (a)–(d): the peeling ODE has a solution,
  unique on `[0, f(μ))`, with all stated properties (`thm34_exists_unique`, `thm34_C1`, `thm34_a`
  to `thm34_d`); Theorem 35, the layer-cake decomposition (`Decomp.decomp`, `Peel.thm35`);
  Theorem 36 (`ConcaveMix.thm36`); and Corollary 39 without hypotheses (`Peel.cor39`,
  `cor39_completelyMixable`: every concave continuous density on `[0, 1]` is `n`-completely
  mixable for every `n ≥ 3`). `ConcaveMix.pconc'` is Theorem 67 with Theorem 36 discharged.
- **Section 20** (`Scaled.lean`, `ScaledB.lean`): the last sentence of Proposition 32
  (`completelyMixable_pieceP`); Theorem 73 (`thm73a`, and `thm73b` with Theorems 27 and 35 as
  hypotheses); Theorem 75 (`thm75`, with Theorem 73(b) for the level law as a hypothesis);
  Corollary 77 (`cor77`); Definition 78 and Theorem 79 (`KPlus`, `thm79`,
  `thm79_completelyMixable`, `KPlus.join`), with Theorem 51 and Theorems 73(b), 67 for the levels
  as hypotheses; Corollary 74 (`cor74a`, `cor74a_sharp`, and `cor74b` with Brunn's theorem as a
  hypothesis); Corollary 80 (`cor80a`, `cor80b`, `cor80b_pentagon`: the constant
  `(5 + 3√5)/2` for the regular pentagon); Remark 81 (`completelyMixable_add_add`,
  `rem81_cyclic`, `rem81_pentagon`: the pentagon is `n`-completely mixable for every `n ≥ 5`);
  Corollary 84 (a), (c), (d), (e). Of Lemma 82 only the analytic part (`lemma82_identity` and
  others) and of Theorem 83 only the one-dimensional parts (`thm83_fibre_max` and others) are
  proved; Theorem 83 for the body and the frustum as a member of `𝒦⁺` are not formalised.
- **Theorem 27, Corollaries 28, 30** (`Theorem27.lean`): the joint mixability of concave
  distribution functions with finite means not all zero exactly when every `F_j` vanishes on
  `(s, ∞)` (`thm27_concave`, `thm27` for the class `D(B)`, `necessity`), with the explicit joint
  mix assembled from Lemmas 17, 18, 22, 23 and Propositions 24, 26 (`pieceMix_spec`,
  `procMix_spec`); Corollary 28 (`cor_cm`, `cor_cm_concave`) and Corollary 30 (`cor30`). For scaled
  copies of one law the mix is a Borel function of the scales and a uniform sequence
  (`scaled_unif_rep`). This discharges the Theorem 27 hypotheses elsewhere: `thm27Frustum`
  (frusta, cones, Theorem 61), Corollaries 44, 45 without hypotheses
  (`simplex_jointlyMixable_iff'`, `simplex_completelyMixable_iff'`,
  `pyramid_completelyMixable_iff'`), Theorem 73(b) (`thm73b_of_thm27`), and, in
  `Unconditional.lean`, Corollary 58 for truncated pyramids and frusta over balls and Theorem 61
  (`classK_completelyMixable` and others) without hypotheses. Corollary 64 holds with
  `cor30 n` for its hypothesis.
- **Hypotheses discharged** (`Bridges.lean`): Theorem 67 without hypotheses (`pconc`: for
  `g ≥ 0` concave and continuous and `p ≥ 1`, the density `g^p` is `n`-completely mixable for
  `n ≥ p + 2`); Theorem 73(b) as a scaling property with constant `p + 2` for `g^p`
  (`scalingProperty_rpow`) and the level laws (`scalingProperty_levLaw`); Theorems 75, 79,
  Corollaries 74(a), 77, 80 without hypotheses (`thm75`, `thm79`, `thm79_completelyMixable`,
  `cor74a`, `cor77`, `cor80a`, `cor80b`), and Corollary 74(b) with Brunn's theorem as the only
  hypothesis (`cor74b`); Lemma 89 for `n ≥ d + 2` without the asymmetry hypothesis (`room`,
  from Remark 85); Corollary 64 (`cor_monotone_a`, `cor_monotone_b`); Corollary 99 (a) in every
  dimension and the regular polytopes of (c) with Theorem 51 proved (`partA`, `dodecahedron`,
  `icosahedron`, `cell24`, `cell600`, `cell120`); and the finiteness in Corollary `j:cor:finite`
  (`procMix_segMix`: at most `8·2^(n−1)` segments per tuple of pieces; `pieceMix_segMix`).
- **Lemma 82, Theorem 83, Corollary 84(b)** (`ScaledC.lean`): the level construction of Lemma 82
  (`levels82`, `levels82_paper`; for `h = 1/2` it is Lemma 69, `levelMix82_half`); Theorem 83 for
  the body `{(z, y) : |z| ≤ 1, y ∈ r(z)F}`: for `F` with the scaling property, `U(K)` is
  `n`-completely mixable for every `n ≥ 2` (`thm83`, with the explicit 3-complete mix
  `thm83_three`); Corollary 84(b) (`cor84b`). The frustum over a convex member of `𝒦⁺` is in
  `𝒦⁺` (`KPlus_frustum`); the full inclusion is `KPlusIncl.inK_subset_kPlus`; Corollary 84(f) is in `Flat.lean`.
- **Definition 90, Theorem 91 (in part), Corollary 93** (`Robust.lean`): the kernel argument
  (`pexider_local`, `glue_affine`, `kernelAffine_of_asym`), which gives the uniqueness in
  Proposition 106 without hypotheses (`prop106_unique_of_asym`: for `n ≥ 3` and `as(K) < n − 1`
  the density of a conditioned product that is a complete mix of `U(K)` is unique up to an
  exponential-affine factor); robust complete mixability (`RobustlyCM`, Definition 90) and its
  consequence of Lemma 92 (`robust_of_symm`); the Hilbert-space core of Theorem 91 (`spectral_gap`,
  `solve_of_gap`, `linear_correction`). Theorem 91 itself is the hypothesis `Thm91Stmt` of
  Corollary 93 (a), (b), (c) (`cor93a`, `cor93b`, `cor93c'`; the ball is robustly completely
  mixable, `ball_robust'`). Not formalised: the operator of Theorem 91 as a multiplication plus a
  compact integral operator, its kernel on `𝒯^ρ(K₀)`, the perturbation and `L∞` estimates.
- **Propositions 108, 109, 117** (`Masking.lean`): total variation against means and translations
  (`prop109_a`, `prop109_b`, `prop117_a`, `prop117_b`), Proposition 109(c) for cyclic mixes
  (`prop109_c_cyclic`), the projection bound `|K \ (K + t)| ≤ ‖t‖·|P_{t⊥}K|` for convex `K` in
  every direction (`volume_sdiff_tr_le_proj_dir`, `tfun_le_proj_dir`), and the bound
  `L′ ≤ L + ε_n` with Theorem 113 as a hypothesis (`prop117_thm113`).
- **Lemma 119, Theorems 120, 121, Corollary 122, Proposition 123** (`Markov.lean`): Proposition
  123 (`prop_price`, `prop_price_tv`); Lemma 119 (`lem_mean`, `lem_mean_markov`); invariant laws
  of Feller kernels on compact sets exist (`exists_invariant_of_feller`, Krylov–Bogolyubov with
  Prokhorov) and are unique under Doeblin's condition (`doeblin_unique`); Theorem 120 (`thm120_a`,
  `thm120_b`) with the measurable selection theorem as the hypothesis `BorelSelection`;
  Corollary 122 without hypotheses (`cor_ball_invariant`, `cor_ball`: for `n ≥ 2/(1 − ρ)` a
  Markov step kernel of joint mixes of the balls and a stationary complete mix of the invariant
  law); Theorem 121 (`thm121_a` with Theorem 113 as a hypothesis, `thm121_b` with the weak
  continuity of the step kernel as a hypothesis).
- **Theorem 95 (in steps), Corollary 96** (`Poly.lean`): Corollary 96(a) for `k ≥ 8` in exact
  arithmetic (`cor96a_ge_eight`) and for `k = 7` from the corner-area bound (`cor96a_seven`);
  Corollary 96(b) from the Riemann-sum bounds of `a₄`, `a₅`, `c₄` and the monotonicity of `a₄`,
  `a₅` as hypotheses (`cor96b_four`, `cor96b_four_eight`, `cor96b_five`); the steps of Theorem 95:
  the Fourier bound for monotone functions (`abs_integral_antitone_mul_cos_le`), the Neumann series
  (`neumann`), (21) implies (22) (`pointwise_of_cond21`), the marginal of the operator `G` and of
  the corner partners (`marginal_withDensity_sum`, `corner_marginal`), and the assembly of the
  complete mix (`completelyMixable_of_densities`); Corollary 96(d) (`cor96d`) with Theorem 95,
  the cases of (c) and the cited facts as hypotheses. Not formalised: the measure on the tuples
  and its densities, the Fourier expansion of `ν` and the construction of `φ`, so the chain from
  condition (21) to complete mixability of `U(P_k)` is not closed.
- **Theorem 95, Corollary 96(d) closed** (`PolyB.lean`): for the concrete regular `k`-gon `poly k`
  (area `k tan(π/k)`, `volume_poly`), the tuple measure and its one- and two-point densities, the
  Fourier expansion (`fourier_ae`, from Mathlib's `L²` theory), the mode estimates
  (`norm_Top_le`, `norm_proj_nu_le`), the Neumann series per mode (`mode_solve`) and the correction
  `φ` (`exists_phi`); hence `thm95`: condition (21) implies `n`-complete mixability of `U(P_k)`.
  `cor96d_poly`: `U(P_k)` is `n`-completely mixable for every `k ≥ 3` and `n ≥ 3`, and
  `cor96d_poly_iff`: for `n ≥ 2` exactly when `n ≥ 3` or `k` is even
  (`completelyMixable_two_iff_even` without hypotheses). Hypotheses of `cor96d_poly`:
  Prékopa–Leindler in the form `PLHyp` (the radial profiles of the `λ_m` do not increase; now proved,
  `PrekopaLeindler.plHyp`); the
  paper's floating-point bounds on `a₄`, `a₅`, `c₄` and the `k = 7` corner area; the four cases
  of (c) as `Cond22` (the Table 15 check); and the triangle, square and hexagon for `n = 3, 4, 5`,
  which are proved elsewhere in this repository (Corollary 44, Lemma 50) in other coordinates and
  not yet transported to `poly 3`, `poly 4`, `poly 6`.
- **Proposition 87** (`Quad.lean`): for a convex quadrilateral that is not a trapezoid and in
  which neither diagonal bisects the other, every sliced 3-complete mix forces chords parallel to
  no side and no diagonal, a chord-midpoint curve made of three segments from one apex to the
  other with the centroid on the middle one, and, when the centroid is inside the middle segment
  and the outer segments are not parallel, equal areas of the two outer parts and
  `3c − P₀ − P₃` on the middle segment (`prop87_quad`); the reduction to chord coordinates is
  `rep_all`, `hull_eq`, `sliced_of_body`.
- **Lemma 103, steps of Theorem 104** (`LLT.lean`): the local limit theorem for densities,
  uniformly over a class with bounded densities and supports, a covariance lower bound and a
  uniform Fourier gap (`lemma103_eps`, with the explicit bound `llt_bound`, and `lemma103_delta`),
  from Fourier inversion for convolution powers (`convPow_eq_inv`, `hatC_sq`, `fourier_convPow`)
  and a Taylor bound (`hatC_taylor`); for Theorem 104 the fixed-point step
  (`completelyMixable_of_marg`: an exponential-affine marginal gives a complete mix of `U(K)`),
  the marginal of the conditioned product (`condMeas_marg`), and the Lipschitz bounds
  (`lip_log_convPow`, `l1_modulus`, `vol_diff_translate`). Theorem 104 itself (the map `Ψ`, its
  compactness and continuity, Schauder's theorem) is not formalised, so Corollary 105 keeps it as
  the hypothesis `Thm104T`.
- **Lemma 112** (`Thm113.lean`): the local limit theorem for sums of different densities of the
  class `𝓗`, uniformly over the class (`llt_eps`, `llt_delta`, with `llt_near`, `gauss0_ge`), the
  covariance bounds (`InH.varF_le`, `InH.varF_ge`), and the inclusion of the class `𝒢` of
  Theorem 113 (`InH.of_InG`); no cited result is assumed. Theorem 113 itself (the map `Φ`,
  compactness, Schauder's theorem) is not formalised, so Corollaries 114, 115 and Theorem 121(a)
  keep it as a hypothesis.
- **𝒦 ⊂ 𝒦⁺** (`KPlusIncl.lean`): every member of the class `𝒦` of Definition 60 is a member of
  `𝒦⁺` of the same dimension (`inK_subset_kPlus`, by induction over the class), so Theorem 79
  recovers the constant `d + 1` of Theorem 61 (`classK_scaling_of_kPlus`,
  `classK_completelyMixable_of_kPlus`).
- **Proposition 71(a)** (`Reduce.lean`): complete mixability passes to weak limits of laws on a
  common compact set (`completelyMixable_of_tendsto`, by Prokhorov and the portmanteau theorem);
  if convex bodies `K_j → K` in the Hausdorff metric and every `U(K_j)` is `n`-completely
  mixable, so is `U(K)` (`reduce_a`); every convex body is a Hausdorff limit of polytopes
  (`exists_polytopes_tendsto`); hence Open Problem 5 in `ℝ^d` holds if and only if it holds for
  polytopes (`op5_iff_polytopes`).
- **Theorem 70, Corollary 99(b)** (`Bipyr.lean`): Theorem 70 with the explicit 3-complete mix
  (`thm70_three`, `thm70`); without hypotheses, bipyramids over centred ellipsoids and
  parallelotopes in dimension at least 3 (`bipyr_ellipsoid`, `bipyr_parallelotope`), the regular
  octahedron (`octahedron`) and the double cones (`dcone_completelyMixable`) are `n`-completely
  mixable for every `n ≥ 2`; Corollary 99(b) for the cross-polytopes without hypotheses (`cor99b`,
  `cor99b_four`: `ℝ⁴`, every `n ≥ 2` except 3; `cor99b_five`: `ℝ⁵`, every `n ≥ 2` except 3, 5).
- **Corollary 68** (`Proj.lean`): for a convex body `K` of dimension `d ≥ 2` and a nonzero linear
  functional `u`, the law of `u(X)`, `X ∼ U(K)`, is `n`-completely mixable for every `n ≥ d + 1`
  (`cor68`, with Brunn's theorem as the hypothesis `BrunnSections`; without it, `PrekopaLeindler.cor68_pl`), and for a cone over a base
  on which `u` is constant not for `n ≤ d` (`cor68_cone`, without hypotheses); Theorem 67 for a
  density `h^p` with `h` concave on an open interval (`pconc_Ioo`).
- **Corollary 84(f)** (`Flat.lean`): the regular `2m`-gons with `2m ≤ 18`, sliced perpendicular to
  two opposite sides, satisfy (P_h) and (F_h) at the values of `h` of the paper's table, proved
  in exact arithmetic (`table_conditions`), so the regular hexagon, octagon, decagon, 12-, 14-,
  16- and 18-gon are `n`-completely mixable for every `n ≥ 2` (`cor84f`, `cor84f_named`).
- **Theorem 104, Corollary 105** (`LLTB.lean`): Theorem 104 as `Thm104T` (`thm104T`) with
  Schauder's fixed-point theorem, which Mathlib lacks, as the hypothesis `SchauderFPT`; the
  uniform Fourier gap for bodies between `B` and `dB` without hypotheses (`fourierGapJohn`); hence
  Corollary 105 (`cor105_full`): for every `d ≥ 1` there is `N_d` such that the uniform
  distribution on every convex body in `ℝ^d` is `n`-completely mixable for every `n ≥ N_d`,
  assuming only John's theorem and Schauder's theorem.
- **Theorem 113, Corollaries 114, 115, Theorem 121(a)** (`Thm113B.lean`): `thm113` and
  `thm113Sym` prove `Large.Thm113` and `Large.Thm113Sym` for any Haar measure, with Tychonoff's
  fixed-point theorem in `ℝ^ι` (product topology), which Mathlib lacks, as the hypothesis
  `TychonoffFP`; `cor114'` (also assuming John's theorem), `cor115'` and `thm121_a'` restate
  Corollaries 114, 115 and Theorem 121(a) with Theorem 113 discharged.
- **Theorem 91, Corollary 93** (`RobustB.lean`): `thm91` proves `Robust.Thm91Stmt V (k+2)`, with
  Hilbert–Schmidt compactness (a bounded measurable kernel on a finite measure space gives a
  compact operator on `L²`), which Mathlib lacks, as the hypothesis `HSCompact`, and the kernel
  step `KernelHyp V`, proved for every finite-dimensional inner product space
  (`kernelHyp_inner`) and for `ℝ × ℝ` (`kernelHyp_prod`); `cor93a`, `cor93b`, `cor93c` restate
  Corollary 93 (a), (b), (c) with only `HSCompact`: a body near a non-triangular body with an
  affine symmetry of order 3 is 3-completely mixable, and bodies near the disc or a ball of
  dimension `≥ 2` are `n`-completely mixable for every `n ≥ 3`.
- **Lemma 49** (`Polygon.lean`): `lemma49`, the planar vectors of lengths `λ_j` summing to `0`.
- **Lemma 54** (`Frustum.lean`): `akq_eq`, `muKQ_ge`, `muKQ_lt_one`, `akq_le`, `akq_eq_iff`,
  `two_lt_akq`.
- **Theorem 62 and Corollary 64** (`Homothetic.lean`): the slicing of a body with homothetic
  sections (`unifSet_body_eq`), the complete mix assembled from a mix of the levels and a section
  mixer (`isCompleteMix_homMix`), the convexity statement (`convex_body`), and Corollary 64(a), (b)
  (`cor_monotone_a`, `cor_monotone_b`). The sufficiency part of Corollary 30 is taken as the
  hypothesis `Cor30 n`, and the section mixer (the scaling property at `t = 0`) as a hypothesis of
  Theorem 62, as in the paper.
- **Lemma 55, Theorem 56, Corollaries 57, 58** (`FrustumMix.lean`): the slicing of a frustum
  (`unifSet_frustumSet`), the necessity of the level condition (`frustum_level_necessity`), the
  sufficiency (`frustum_sufficiency`) and the scaling property of the frustum
  (`frustum_scalingProperty`); for truncated simplices both necessary conditions and the
  threshold `n ≥ k + 1` (`tsimplex_necessity`, `tsimplex_completelyMixable_le`,
  `tsimplex_completelyMixable_iff`), Corollary 44 by induction (`simplex_scalingProperty`); for
  frusta over cubes and balls the threshold `n ≥ a_{d,q}` (`frustum_completelyMixable_le`,
  `pyramid_necessity`, `circCone_necessity`, `circCone_completelyMixable_iff`). The necessity
  directions are unconditional. The sufficiency directions take Theorem 27 for the level laws,
  with Borel dependence on the parameters (`Thm27Frustum`), as a hypothesis, and for cubes and
  balls also their scaling property with constant 2.
- **Lemmas 63, 66, 76** (`Means.lean`): `brunn_mean`, `root_concaveOn`, `root_mean`,
  `weighted_mean` (with its equality case), on top of Chebyshev's covariance inequality for
  integrals (`chebyshev_pairwise`, `chebyshev_monotoneOn`).
- **Lemma 69, Theorem 67, Proposition 71** (`Bipyramid.lean`): Lemma 69 in full (`key_identity`:
  `α + 2b = 3ν`; `levels`: `α ≥ 0`, `∫ α = 1`, and the explicit 3-complete mix of the symmetric
  level distribution with sum 0 and at least two levels in `[−1/2, 1/2]`); Theorem 67 (`beta_le`:
  `β ≤ p + 2` along the peeling; `pconc`, with Theorems 34 and 36 as the hypotheses
  `PeelingProps` and `H36`); Proposition 71(c) (`reduce_c`, `reduce_c2`); Proposition 71(a)
  (`completelyMixable_of_tendsto`: limits of `n`-completely mixable laws on a common compact set,
  by Prokhorov's theorem; `reduce_a`, with the convergence of the uniform distributions as a
  hypothesis).
- **Proposition 86** (`Square.lean`): `no_polygon_complete_mix`, with the certificate at
  `x₀ = 1/8` and its integral.
- **Lemmas 88, 89, 92 and the fibre inequality of Theorem 70** (`Room.lean`): Lemma 88
  (`completelyMixable_iff_tuples`, `completelyMixable_unif_iff`), Lemma 89 (`room`, with the
  constants of the paper; in the plane `planar_asym`: `as(K) ≤ 2`, with `as(K) < 2` unless `K` is
  a triangle, and `room_planar_three`), Lemma 92 (`symm_room`, `symm_robust`), and the fibre
  inequality (`fibre_core`, `fibre_triple`). In dimension `d > 2` the Minkowski–Radon bound
  `as(K) ≤ d` is a hypothesis.
- **Proposition 98** (`Symm.lean`): `symmDensity_nonneg_iff`, `symmMeasure_identity`,
  `completelyMixable_mul`, `completelyMixable_add`, `completelyMixable_centralSymm`.
- **Corollary 99** (`SymmCor.lean`): (a) centrally symmetric bodies (`partA`; in the plane every
  `n ≥ 2` except 3, `partA_plane`; in space every `n ≥ 2` except 3 and 5, `partA_space`);
  (b) cross-polytopes (`partB`, `partB_four`, `partB_five`, with the volumes and `243 < 25π²`);
  (c) bodies whose inscribed ball is large (`ball_core`), the dodecahedron, the icosahedron, the
  24-cell, the 600-cell and the 120-cell; (d) bodies with an affine symmetry of order 3
  (`partD`, `partD_plane`). Ball's volume-ratio theorems with John's ellipsoid, the sufficiency in
  Theorem 51, Theorem 70, the Brunn–Minkowski inequality (since proved in `PrekopaLeindler.lean`) and the classical volumes and inradii of
  the regular polytopes are hypotheses; the numerical inequalities are proved.

### Further open questions (the sections on asymmetric windows, projections, the norm condition and lattices)

- **Lemma `as:lem:tilt`, Proposition `as:prop:window`** (`AsymWindow.lean`): `lemTilt` (the tilted
  density `P_{H,γ}` has an `m`-complete mix with sum `mγH/2` for `m ≥ 4, |γ| ≤ 1` and for
  `m = 3, |γ| ≤ 2/3`, with a measurable kernel in `γ`: `tiltKH_spec`, `measurable_tiltKH`), the
  identity `as:eq:affine` (`eq_affine`), and the window proposition in dimension `d`
  (`propWindow`), on the line (`propWindowReal`) and for `m = 3` (`propWindowThree`).
- **Lemma `as:lem:conc`, Theorem `as:thm:window`, Corollary `as:cor:interval`** (`AsymThm.lean`,
  `Steinitz.lean`): (a) `lem_conc_a`, (b) `lem_conc_b`, (c) `lem_conc_c_uncond`; the window
  theorem in every dimension (`thm_window_all`, on the line `thm_window_one_proved`); the
  corollary (`cor_interval_proved`, `cor_interval_n_proved`, `cor_interval_density_proved`). The
  Steinitz lemma with constant `d` (Grinberg–Sevastyanov) is proved in every finite-dimensional
  normed space (`steinitz_normed`).
- **Theorem `as:thm:general`, Corollaries `as:cor:body`, `as:cor:order`** (`AsymGeneral.lean`,
  `AsymBridge.lean`): `thm_general_b`, `thm_general_mix_b`, `cor_order_b`, and `cor_body_b`
  (`N*(2) = 579`, `N*(3) = 27548`), which takes John's theorem (`JohnThm`) as a hypothesis.
- **Propositions `as:prop:complete`, `as:prop:three`, Corollaries `as:cor:repeat`,
  `as:cor:three`, Remark `as:rem:three`** (`AsymThree.lean`, `ConvSq.lean`, `TwoStepBorel.lean`,
  `AsymBridge.lean`): `prop_complete_b`, `prop_complete_dirac_b`, `four_uniform_jointlyMixable_b`,
  `cor_repeat_b`, `prop_three_b`, `cor_three_b`, `cor_three_mixable_b`, `cor_three_a_b`,
  `cor_three_b_b` (the theorem of Puccetti, Wang and Wang), `cor_three_c_b`, `rem_three_b`. The
  step `G ∗ G ≥ q U` for a law with a nonzero absolutely continuous part (`convSq`) and the Borel
  dependence of the two-step complete mixes on their parameters (`twoStepBorel`) are proved.
- **Theorem `as:thm:hetero`, Corollary `as:cor:hetero`** (`AsymHetero.lean`, `AsymBridge.lean`):
  `thm_hetero_b`, `thm_hetero_strong_b`, `thm_hetero_jointlyMixable_b`, `cor_hetero_b`,
  `cor_hetero_jointlyMixable_b`, `cor_hetero_n_b`.
- **Lemmas `pj:lem:three`, `pj:lem:example`, `pj:lem:gadget`** (`ProjLemmas.lean`): `three_a`,
  `three_b`, `ex_not_jointlyMixable`, `ex_map_jointlyMixable`, `gadget_a`, `gadget_b`.
- **Theorem `pj:thm:main`, Corollary `pj:cor:confine`, Remark `pj:rem:positive`**
  (`ProjMain.lean`): a smooth compactly supported density (`pj_thm_main_uncond`) and an
  everywhere positive real-analytic density (`pj_thm_main_analytic_uncond`) whose images under
  all linear maps with a nontrivial kernel are `n`-completely mixable while the law itself is not;
  projections onto proper subspaces (`pj_thm_main_proj_uncond`); the corollary
  (`pj_cor_confine_uncond`); products (`rem_product`). Analyticity of Gaussian smoothings is proved
  through an explicit power series (`laplace_analytic`).
- **Lemmas `nc:lem:peak`, `nc:lem:count`, Proposition `nc:prop:atom`, Corollary `nc:cor:least`**
  (`NormAtom.lean`, `StopLoss.lean`): `peak`, `peak_interval`, `peak_completelyMixable`,
  `count_lemma`, `count_lemma_reflect`, `atom_completelyMixable_iff`, `atom_stopLoss`,
  `atom_cx_uncond`, `cor_least_iff`, `cor_least_explicit_uncond`, `cor_least_exists_uncond`. That
  the stop-loss order with equal means and bounded support implies the convex order
  (Shaked–Shanthikumar) is proved (`stoploss_cx`). The norm inequalities take the cited theorem of
  Shmalo (`H_shmalo26b`) as a hypothesis.
- **Theorem `nc:thm:unimodal`, Corollary `nc:cor:alln`** (`NormUnimodal.lean`, `AsymBridge.lean`):
  `cxCond_of_SL_b`, `cx_F1_F2_b`, `cor_alln_mixable_b`, `threshold_unimodal_b`; with Shmalo's
  theorem as a hypothesis, `normIneqs_of_SL_b`, `thm_unimodal_norm_b`, `cor_alln_norm_b`.
- **Lemma `lt:lem:count`, Propositions `lt:prop:ops`, `lt:prop:three`, Theorem `lt:thm:pb`**
  (`LatticeBasic.lean`): `count_iff_fintype`, `ops_a`, `ops_b`, `ops_c`, `three_cm_iff`,
  `binom2_cm_iff`, `binom_completelyMixable`.
- **Theorem `lt:thm:large`, Proposition `lt:prop:binomial`, Remark `lt:rem:necessary`**
  (`LatticeLarge.lean`, `LatticeBridge.lean`): `large_a_uncond`, `large_b_uncond`,
  `large_eventually_uncond`, `large_c_int`, `large_c_two_uncond`, `binomial_a_uncond`,
  `binomial_b_add`, `binomial_b_N0`, `binomial_c_uncond` (the computed cases `n ≤ 10`,
  `N₀ ≤ 12` are 1665 certificates checked by kernel evaluation), `remark_necessary_uncond` (the
  three distributions of the remark). The closing sentence of the remark on the searches is not
  formalised.
- **Proposition `rm:prop:generic` and the new remarks** (`Remarks14.lean`): `prop_generic_a_mix`,
  `prop_generic_b`, `prop_generic_c`, `jointlyMixable_iff_exists_cE`; the remark on Lemma 1
  (`isArchimedesMeasure_sphUnif_uncond`, with the theorem of Archimedes on the projections of the
  uniform distribution on the sphere `S²` proved in `Archimedes.lean`: `archimedes`,
  `sphUnif_map_inner_uncond`), the remark on Theorem 6 (`tau_exchange`, `rho_exchange`,
  `S_no_jump`, `collinear_of_tight`), and the remark on trapezoids (`chord_jointMix`,
  `disc_polygon_fails`).

- **Sharper rate, measurable selection, and combined statements** (`AsymRate.lean`,
  `BorelSelect.lean`, `Combined.lean`): `as:thm:general` and `as:cor:order` for every
  `κ < qH/(4d)` (`thm_general_rate`, `cor_order_rate`); the measurable selection theorem of
  Kuratowski and Ryll-Nardzewski for compact values (`exists_selection`), hence Theorem 120
  without hypotheses (`thm120_a_uncond`, `thm120_uncond`); and single theorems, in the paper's
  coordinates, for Lemma 18 with the paper's merging procedure (`res18`), Theorem 43 (`res43`),
  Corollary 45 (`res45`), Theorem 56 (`res56`), Corollary 57 (`res57`), Corollary 58 (`res58`),
  Lemma 59 (`res59`), Theorem 79 (`res79`) and Proposition 86 with the paper's definition of a
  sliced mix (`res86`).

- **Prékopa–Leindler and Brunn–Minkowski** (`PrekopaLeindler.lean`; neither is in Mathlib):
  Brunn–Minkowski on the line (`bm1`), the Prékopa–Leindler inequality on the line (`pl1`) and in
  `ℝⁿ` and `ℂᵐ` (`prekopa_leindler`, `prekopa_leindler_complex`) for measurable functions with values
  in `[0, ∞]`, by tensorisation of the property along products; the multiplicative and additive
  Brunn–Minkowski inequalities (`bm_mul_of_plProp`, `brunn_minkowski`); Brunn's theorem on the
  concavity of the `1/m`-th power of section volumes of a convex body (`brunnSections`); and the
  hypothesis `PLHyp` of Theorem 95 (`plHyp`). Hence Corollary 68 and Theorem 95 without hypotheses
  (`cor68_pl`, `thm95_pl`, `cm_of_cond22_pl`, `cor96d_poly_pl`).

- **Corollary 74(b) without hypotheses** (`Brunn74.lean`): for a convex body `K` in a space of
  dimension `d ≥ 2` and a nonzero linear functional `u`, the law of `u(X)`, `X ∼ U(K)`, is an affine
  image of a law on `[0, 1]` with density `g^(d-1)`, `g ≥ 0` concave and continuous (`exists_brunn`,
  from `PrekopaLeindler.brunnSections`); hence `cor74b_brunn` and `cor74b_bridges`, Corollary 74(b)
  with Brunn's theorem proved.

No statement treated was found false.

## Differences from the paper

- Lemma 1 uses a probability measure on the unit disc of the plane, with density
  `1/(2π√(1 − |x|²))`, in place of the uniform distribution on the sphere of `ℝ³`; the proof
  shows that its projection on every line is uniform (`isArchimedesMeasure_archPlane`), which is
  all that Lemma 1 uses. That it is the projection of the sphere measure is not proved. The
  general theorems accept any measure with this projection property.
- Lemma 3 is proved for arbitrary joint mixes, not only those of Lemma 1; the random permutation
  is the average over all permutations.
- Theorem 6: the condition `u₂ > (n−2)a` of case (D) is not needed (the construction of case (D)
  works whenever `u₁ > b` and `n = 3` or `u₃ < 0`), and case (B) does not use `b ≤ n`. Lemma 5
  is proved for `0 ≤ u ≤ b`. Densities use half-open intervals, so their identities hold at every
  point. Lemma 4 is proved, but the proof of Theorem 6 computes the coefficients directly.
- Theorem 12 and Corollary 13 assume the density right-continuous (non-increasing case) or
  left-continuous (non-decreasing case); a monotone density can be so chosen up to a null set.
  Lemmas 9 and 10 are proved for a measure `ν` given as data, and Lemma 10 for any law `π` of
  slab lengths. The case `n = 2` needs no separate argument. In the kernel of Theorem 12, Lemma 1
  uses the first partition of a fixed list that satisfies the triangle inequalities; the paper's
  choice only shows that one exists.
- Proposition 32: all four tuples are admissible for every parameter of their case, also when
  their weight is `0`. Its last sentence, the complete mix, follows from `pieces_mixture` and
  Lemma 3 but is not stated separately here.
- Lemma 38 assumes `∫ g > 0` in place of "not identically zero"; its proof uses concavity,
  a change of variables and integration by parts rather than the measure `−h''`.
- Lemmas 63 and 66 hold for every real exponent `γ ≥ 0`; integrability and the positivity of the
  normalising integral are proved, not assumed. Lemma 66 needs `a < b`, which the paper leaves
  implicit.
- Theorem 43(a) holds for any measurable base of finite positive volume, without `n ≥ 2`, without
  "not all `λ_i` zero" and without the scaling property. The simplex and the pyramid are treated
  in normal form; the affine images belong to Corollaries 44 and 45, not formalised here. Of the
  middle claim of Remark 47 only its consequence for trapezoids is proved, directly.
- Theorem 62 is stated for laws: the joint law is the image of the level mix times an
  independent source of randomness, not a Borel function of uniform variables. Corollary 64(b)
  holds for `k ≥ 2`; the paper's `k ≥ 3` is not used.
- Theorem 40: a trapezoid is the convex hull of `P, P + m v, R, R + M v` with `0 ≤ m ≤ M`,
  `M > 0`; the abscissa mix comes from Corollary 13, which is Theorem 12 after the paper's
  change of variable up to an affine rescaling.
- The scaling property is formulated for the measure `U(K)` and shown equal to the paper's form
  for sets of finite positive volume; Lemma 48 for sets is proved for invertible affine maps, and
  for measures for every linear map. The necessity in Theorem 51 compares volumes rather than
  means.
- The frusta are written in coordinates `ℝ × G` as `{(s, s b) : q ≤ s ≤ 1, b ∈ B}`, with `B`
  any measurable set of finite positive volume; the paper's truncated simplices, pyramids and
  frusta over balls are linear images of these sets, but the transfer along that bijection is not
  formalised.
- Lemma 69: the hypotheses "Lipschitz on `[0, 1/2]`" and `ν(1) = 0` are not used, and
  `α(x) = O(x)` near 0 follows from `α ≤ 3ν`; the paper calls the integrand bounded near 0,
  whereas only its numerator is. Theorem 67 is stated on `[0, 1]` for a concave continuous
  `f^{1/p}`; the affine reduction and the unimodality check are not formalised. Proposition 71(c)
  does not need convexity. Proposition 71(a) is in `Reduce.lean`.
- Corollary 99(d) does not need `u_d > 1`; the classification of the regular polytopes and the
  claim for `d ≥ 6` in (c) are not formalised.
- Proposition 24: the marginals are identified by comparing step densities interval by interval
  instead of the balance criterion; `c₁, c₂ > 0` follow from the other hypotheses and are
  dropped. Lemma 18 groups the lengths by cutting them in order at `s`, not by repeatedly merging
  the two shortest; the merging step itself is proved separately.
- Lemmas 20 to 23: `D(B)` is given by its description in Definition 19 (non-increasing,
  right-continuous density, a possible atom at 0); its equivalence with a concave distribution
  function is not formalised. Lemma 21 is split into the cases `a > 0` and `a = 0`. The procedure
  of Lemma 23 runs with an explicit depth bound that is shown never to stop it early.
- Lemma 25 is stated on multisets, and its hypothesis `s > 0` is not used.
- Lemma 88 holds for every `n ≥ 1` and general laws. In Lemma 92 the affine map is replaced by a
  linear one after translating its fixed point to 0, and the constant `b` differs from the
  paper's. The equality case of Lemma 89 integrates a pointwise inequality instead of using
  Chebyshev's inequality.
- Corollary 45 needs Lemma 1's joint mix to depend measurably on the lengths, which the paper
  does not state; it is proved (`scalingProperty_Icc`). Simplices and pyramids may lie in any
  finite-dimensional space of the right dimension.
- Theorem 51 is proved with a different joint mix: for even dimension through the complex
  structure of `ℝ^{2k}`, for odd dimension through a rotation-invariant measure on `ℝ^{j+1}`
  projecting to `U(B_j)`, which avoids the uniqueness on the sphere; the polygon of Lemma 49 is
  formed with the index where the partial sums cross half the total, so that it depends
  measurably on the lengths. The remark after Proposition 52 is not formalised.
- Lemma 59: the hypothesis `m = max(m₁, m₂) ≥ 1` cannot be dropped. For two points with
  `m₁ = m₂ = 0` the join is a segment, and the constant `0` fails for `n = 2`, `λ = (1, 0)`
  (`join_points_not_scaling`).
- Large: conditioned products are measures with a density relative to a reference measure:
  Lebesgue measure on the first `n − 1` coordinates of the hyperplane for Theorem 113 and
  Corollary 114, any finite measure for Proposition 116, its image under the maps `M_j⁻¹` for
  Corollary 115. Corollary 114 needs one common correction `φ`, which the paper takes from the
  proof of Theorem 113, not its statement; this is the hypothesis `Thm113Sym`. In `Thm104T` the
  surface area is bounded through the circumradius inside the hypothesis, and the Fourier
  condition is required for every `r > 0`. The covariance lower bound in Corollary 105 is proved
  with an explicit constant in place of the paper's mixture argument. The closing remark of
  Corollary 115 on complex weights is not formalised. `cent_eq_integral_unifSet` identifies the
  centroid with the one in `Room.lean`, whose Minkowski–Radon hypothesis is thus available as
  `asymLE_cent`.
- Theorem 34: the solution exists by Picard–Lindelöf on a mollified right-hand side and a limit
  argument, not by Peano's theorem; the derivative at `U = 0` is one-sided and uniqueness is
  equality on `[0, f(μ))`; "C¹" for `L` is stated as the two partial derivatives and a uniform
  first-order expansion; part (c) is a pair of measure identities on `(0, f(μ))` for Stieltjes
  functions equal to `A` and `−B` up to constants. `A` and `B` are defined by `sInf` and `sSup`,
  and the paper's case definition is proved. The density, continuous on `[0, 1]`, is extended
  by clamping.
- Section 20: the level coordinate is written first; lower-dimensional members of `𝒦⁺` are
  pushforward measures; Corollary 80(a) is stated for a non-increasing profile (the increasing
  case is a reflection) and the pentagon's `s̄` is an input.
- Theorem 27: the condition `max B_j ≤ s` is stated as `F_j((s, ∞)) = 0`, and `n ≥ 1`
  suffices. At the leaves the lengths are cut in order at `s` (Lemma 18) and one pair with sum at
  most `s` is merged, instead of merging the two smallest groups (Lemma 25); the result is still
  valid input for Propositions 24 and 26. The measurable dependence on the laws is proved for
  scaled copies of one law, which is what every application uses. `thm73b_of_thm27` assumes `β`
  measurable with `β ≥ 2` and `λ ≥ 0`, which `thm73b` leaves implicit; `Thm27Frustum m q` holds
  for `0 ≤ q < 1`, the range used.
- `Bridges.lean`: Theorem 75 and Corollary 77 need `∑ dim V_j ≥ 1` and Corollary 80(a)
  `dim W ≥ 1` (the case `∑ dim = 0`, the level law `U[0,1]`, is not covered), and β* in Theorem
  75 is replaced by the Theorem 67 bound `∑ k + 2`. Lemma 89 keeps the ball about the centroid,
  part of its statement, as a hypothesis. Corollary 99(b) is in `Bipyr.lean`, and (c) the classical volume and inradius data, as hypotheses. In Corollary `j:cor:finite` the
  count is in atoms of the piece laws, not of the slab measures (the step `⌊k²/4⌋ + 1` of Lemma 20
  is inside the existence proof), and the claim about finitely many rational operations is not
  formalised.
- Lemma 82 does not use the Lipschitz property on `[0, h]`, nor `ν(1) = 0` for `h = 1/2`
  (`levels82_paper` keeps them as unused hypotheses); Theorem 83 does not need `F` convex. The
  absolute values of the levels are stated through a permutation, and for `n = 2` the mix comes
  from Theorem 62 with the levels `(S, −S)`.
- `Robust.lean`: the kernel argument is a local Pexider equation solved by smoothing, glued over
  the connected interior, instead of differentiation and the contraction `x ↦ −x/(n − 1)`; the
  spectral gap is proved by norm convergence instead of weak limits; Banach–Mazur closeness is the
  existence of some `1 ≤ t < 1 + ε`. Corollary 93(a) is stated in `ℝ × ℝ` and (b) in `ℂ`; the
  remarks in (b) on regular `k`-gons are not formalised.
- `Markov.lean`: the chain is given by its step kernel and the laws of its iterates, not as a
  path measure; kernels live on the ambient space, with Feller continuity and invariance required
  on `K_j` only. Corollary 122 is stated in `EuclideanSpace ℝ (Fin d)` with the kernel extended off
  the ball by the retraction `y ↦ y / max(1, |y|)`; it needs no selection theorem, since Theorem
  51 gives the mix measurably. In Theorem 121(b) the continuity of `P` comes from the inside of
  the proof of Theorem 113 and is a hypothesis here; the maximal-entropy claim of (a) is not
  formalised. In Proposition 109(c), for an affine `A` the support lies in an affine, not linear,
  subspace; the proof only uses its difference set, which is linear.
- Corollary 96(d): for the octagon with `n = 5`, where condition (21) fails (Table 14), `cor96d`
  uses, as the paper does, that the octagon is centrally symmetric, hence 2-completely mixable,
  and `5 = 2 + 3` (Remark 81). In Corollary 96(a) for `k = 7`, the paper's left side uses the sum `(8/9)·π²/6`; with `π²/6` it is `0.0629`, still
  below the right side.
- Proposition 87: "sliced in direction `e`" is defined in chord coordinates; the segments are
  shown non-collinear from their slopes, and the side case from the trapezoid hypothesis and
  convexity, instead of the affine reflection; that the outer parts are triangles is implicit
  in the affine chord length vanishing at the apices.
- `LLT.lean`: the Gaussian limit is the inverse Fourier transform of `exp(−2π²Q_h)` in Mathlib's
  convention; Lemma 103 is stated for an explicit class rather than `ℋ(K, A)`; the estimate uses
  two regions with an explicit error instead of three; the bounded-variation step is replaced by an
  `L¹` modulus of continuity from a homothety of the convex body.
- Lemma 112: the uniform Fourier gap comes from the ball contained in the bodies, the
  Riemann–Lebesgue lemma and compactness of an annulus, without Blaschke's selection theorem; the
  `L²` bound from Gaussian regularisation and Fatou's lemma; the covariance constant differs from
  the paper's but depends on the same parameters; the lemma is stated for at least two factors.
- 𝒦 ⊂ 𝒦⁺: a frustum over a point and a join of two points are segments, not hulls in the sense of
  Corollary 77 (which needs bases of dimension at least 1); they enter as affine images of the
  1-ball.
- Proposition 71(a): `n ≥ 2` is not needed; the sum condition passes to the limit through the
  constant sums along a subsequence and the portmanteau theorem, without continuity of the
  centroid; the volume step uses almost-everywhere convergence of membership (the frontier of a
  convex set is null) and dominated convergence instead of `|K_j △ K| → 0`; the Hausdorff
  distance is that of the sup norm, which is equivalent.
- Theorem 70: condition (o:eq:starr) includes the integrability of `r^{k−1}/(1 − a)` on
  `[1/2, 1]`; the theorem is obtained as Theorem 83 at `h = 1/2`; ellipsoids and parallelotopes
  are linear images of the ball and the cube.
- Theorem 104: the map `Ψ` is `ψ ↦ log h_ψ^{*m}(0) − log h_ψ^{*m}(−·)` without a projection onto
  affine functions (the mean-zero tilt absorbs the affine part); its continuity is proved by a
  Lipschitz bound rather than by compactness; the surface area is replaced by an `L¹` modulus;
  the decay of `ψ_n` and the robustness are not stated separately.
- Theorem 113: no projection `P_j`; the unknown is the family of corrections with `|ψ_j| ≤ 1`
  and `Lip(ψ_j) ≤ 1` on `K_j`, compact by Tychonoff's theorem, so Arzelà–Ascoli is not needed; the
  tilt is recomputed from `ψ` by Lemma 111(b) and vanishes at the fixed point by Lemma 111(c); the
  Lipschitz estimate uses the `L¹` modulus of one factor with Lemma 112, without the constant
  `C₁`; Lemma 112 and the `L¹` modulus are transferred to any Haar measure.
- Theorem 95 (`PolyB.lean`): indexing `n = m + 3`; `thm95` takes any bound `N` of `ν` on `B`, so
  both forms of `N` are covered; `Gφ = −ν_o` holds almost everywhere, which suffices for
  densities; `φ` is the real part of the series.
- Theorem 91 (`RobustB.lean`): the correction lives on a fixed inner body `D = (K₀)_ρ`, so the
  operator `G = S*S` on `L²(D)` does not depend on `K` and the paper's perturbation estimate and
  extension step are not needed; the linear defect is solved by a spectral gap (bounded-below plus
  compact part) and an `L∞` bootstrap; partners are a point reflection plus offsets uniform on a
  product of balls.
- Lemma 49 omits the hypothesis `n ≥ 2`, which the other hypotheses imply.
- Proposition 86: the phrase "no sliced mix" is not formalised, since "sliced" is not defined.
- Proposition 98: `K` and `L` need only be measurable with `0 < |L|` and `|K| < ∞`; convexity,
  compactness and the centroid are not used, and `m ≠ 0` replaces `m ≥ 2`.
- Further open questions: "explicit" random variables are not formalised, only the existence
  of the mixes; `prop_complete_b` assumes `ℓ ≥ 0`, which in the paper follows from `K ≥ 1`;
  `as:thm:general` is proved for every `κ < qH/(4d)` (`AsymRate.thm_general_rate`);
  `as:thm:hetero` is also proved with the stronger window `m₂H/2 − ℓ`; in `pj:thm:main` the
  Gaussian smoothing exists for `δ = 1/(k+1)`, `k` large.

## What to read

`Mixes/Defs.lean` (the definitions), then the files named above.

# Programs

The folder `programs/` contains the Python programs behind the numbers, tables and figures of the
paper, with their stored output; see `programs/README.md`.

# Checking the proofs

Install Lean with [elan](https://github.com/leanprover/elan), then:

```bash
git clone <this repository>
cd <repository folder>
lake exe cache get        # download the compiled Mathlib
lake build                # checks every proof
lake env lean Verify.lean # prints the axioms the main theorems use
```

`Verify.lean` should print `[propext, Classical.choice, Quot.sound]` for every theorem (a few
need only `propext`): the standard axioms of Lean and Mathlib, and no `sorryAx`. The GitHub
Actions workflow runs the same two steps on every push. No proof uses `sorry` or
`native_decide`.

Lean `v4.37.0-rc1` and the Mathlib version are fixed by `lean-toolchain` and `lake-manifest.json`.
