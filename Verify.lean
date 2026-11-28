import Mixes

/-!
# Verification

Prints the main statements and the axioms their proofs depend on.  Each line should read
`[propext, Classical.choice, Quot.sound]`, the standard axioms of Lean and Mathlib (a few
statements need only `propext`); an unfinished proof (`sorry`) would show up here as `sorryAx`.

Run with `lake env lean Verify.lean` after `lake build`.
-/

-- Mixes: explicit complete and joint mixes (Parts I, II, IV)
#check @Mixes.trap_polygon
#check @Mixes.trap_meancond
#check @Mixes.trap_const_sum
#check @Mixes.trap_nh_eq_two_iff
#check @Mixes.akq_eq
#check @Mixes.akq_le
#check @Mixes.two_lt_akq
#check @Mixes.SquareSlice.no_polygon_complete_mix
#check @Mixes.PolygonL49.lemma49
#check @Mixes.pieces_mixture
#check @Mixes.mean_mem_middle_third
#check @Mixes.chebyshev_pairwise
#check @Mixes.brunn_mean
#check @Mixes.root_concaveOn
#check @Mixes.root_mean
#check @Mixes.weighted_mean
#check @Mixes.isArchimedesMeasure_archPlane
#check @Mixes.lem_arch
#check @Mixes.lem_sym
#check @Mixes.completelyMixable_mixtureMarginal'
#check @Mixes.TwoStep.thm6_measure
#check @Mixes.TwoStep.cor7
#check @Mixes.completelyMixable_g
#check @Mixes.completelyMixable_add
#check @Mixes.completelyMixable_centralSymm
#print axioms Mixes.trap_polygon
#print axioms Mixes.trap_meancond
#print axioms Mixes.trap_const_sum
#print axioms Mixes.trap_nh_eq_two_iff
#print axioms Mixes.akq_eq
#print axioms Mixes.muKQ_ge
#print axioms Mixes.muKQ_lt_one
#print axioms Mixes.akq_le
#print axioms Mixes.akq_eq_iff
#print axioms Mixes.two_lt_akq
#print axioms Mixes.SquareSlice.no_polygon_complete_mix
#print axioms Mixes.SquareSlice.integral_cert
#print axioms Mixes.PolygonL49.lemma49
#print axioms Mixes.pieces_mixture
#print axioms Mixes.caseI_marginal
#print axioms Mixes.caseII_marginal
#print axioms Mixes.mean_mem_middle_third
#print axioms Mixes.chebyshev_pairwise
#print axioms Mixes.brunn_mean
#print axioms Mixes.brunn_mean_rpow
#print axioms Mixes.root_concaveOn
#print axioms Mixes.root_mean
#print axioms Mixes.weighted_mean
#print axioms Mixes.weighted_mean_eq
#print axioms Mixes.isArchimedesMeasure_archPlane
#print axioms Mixes.lem_arch
#print axioms Mixes.lem_sym
#print axioms Mixes.exists_lem_arch_admissible
#print axioms Mixes.completelyMixable_mixtureMarginal'
#print axioms Mixes.TwoStep.thm6_i
#print axioms Mixes.TwoStep.thm6_ii
#print axioms Mixes.TwoStep.thm6_measure
#print axioms Mixes.TwoStep.cor7
#print axioms Mixes.TwoStep.recog_measure
#print axioms Mixes.completelyMixable_g
#print axioms Mixes.symmDensity_nonneg_iff
#print axioms Mixes.symmMeasure_identity
#print axioms Mixes.completelyMixable_mul
#print axioms Mixes.completelyMixable_add
#print axioms Mixes.completelyMixable_centralSymm
#check @Mixes.unifSet_scaledCone_split
#check @Mixes.cone_jointlyMixable_le
#check @Mixes.simplex_completelyMixable_le
#check @Mixes.trap_completelyMixable_two_iff
#print axioms Mixes.unifSet_scaledCone
#print axioms Mixes.unifSet_scaledCone_bind
#print axioms Mixes.unifSet_scaledCone_split
#print axioms Mixes.unifSet_scaledCone_ae_reconstruct
#print axioms Mixes.cone_jointlyMixable_le
#print axioms Mixes.cone_completelyMixable_le
#print axioms Mixes.simplex_completelyMixable_le
#print axioms Mixes.pyramid_completelyMixable_le
#print axioms Mixes.completelyMixable_two_iff
#print axioms Mixes.trap_completelyMixable_two_iff
#check @Mixes.Homothetic.isCompleteMix_homMix
#check @Mixes.Homothetic.cor_monotone_b
#print axioms Mixes.Homothetic.unifSet_body_eq
#print axioms Mixes.Homothetic.isCompleteMix_homMix
#print axioms Mixes.Homothetic.convex_body
#print axioms Mixes.Homothetic.levels_mixable
#print axioms Mixes.Homothetic.cor_monotone_a
#print axioms Mixes.Homothetic.cor_monotone_b
#check @Mixes.Slabs.slab_lemma
#check @Mixes.Slabs.pairs_lemma
#check @Mixes.SlabsMix.mono_mix
#check @Mixes.SlabsMix.mono_completelyMixable
#check @Mixes.SlabsMix.cor13_nonincreasing
#print axioms Mixes.Slabs.layer_cake
#print axioms Mixes.Slabs.slab_lemma
#print axioms Mixes.Slabs.exists_nu
#print axioms Mixes.Slabs.pairs_lemma
#print axioms Mixes.SlabsMix.Q0_spec
#print axioms Mixes.SlabsMix.kappa_spec
#print axioms Mixes.SlabsMix.gMeas_eq
#print axioms Mixes.SlabsMix.mono_mix
#print axioms Mixes.SlabsMix.mono_completelyMixable
#print axioms Mixes.SlabsMix.cor13_nonincreasing
#print axioms Mixes.SlabsMix.cor13_nondecreasing
#check @Mixes.Assembly.completelyMixable_trapezoid'
#check @Mixes.ball_necessity
#check @Mixes.completelyMixable_prod_iff
#print axioms Mixes.Assembly.unifSet_trapSet_eq
#print axioms Mixes.Assembly.chordVec_spec
#print axioms Mixes.Assembly.trapMix_isCompleteMix
#print axioms Mixes.Assembly.completelyMixable_trapAbsc
#print axioms Mixes.Assembly.completelyMixable_trapezoid'
#print axioms Mixes.scalingPropertySet_image_affine
#print axioms Mixes.scalingPropertySet_prod
#print axioms Mixes.completelyMixable_prod_iff
#print axioms Mixes.ball_necessity
#check @Mixes.FrustumMix.frustum_level_necessity
#check @Mixes.FrustumMix.frustum_sufficiency
#check @Mixes.FrustumMix.tsimplex_completelyMixable_iff
#print axioms Mixes.FrustumMix.unifSet_frustumSet
#print axioms Mixes.FrustumMix.frustum_level_necessity
#print axioms Mixes.FrustumMix.frustum_sufficiency
#print axioms Mixes.FrustumMix.frustum_scalingProperty
#print axioms Mixes.FrustumMix.tsimplex_necessity
#print axioms Mixes.FrustumMix.tsimplex_completelyMixable_le
#print axioms Mixes.FrustumMix.simplex_scalingProperty
#print axioms Mixes.FrustumMix.tsimplex_completelyMixable_iff
#print axioms Mixes.FrustumMix.frustum_completelyMixable_le
#print axioms Mixes.FrustumMix.pyramid_necessity
#print axioms Mixes.FrustumMix.circCone_necessity
#print axioms Mixes.FrustumMix.circCone_completelyMixable_iff
#check @Mixes.Bipyramid.levels
#check @Mixes.Bipyramid.pconc
#check @Mixes.Bipyramid.reduce_c
#print axioms Mixes.Bipyramid.beta_le
#print axioms Mixes.Bipyramid.pconc
#print axioms Mixes.Bipyramid.pconc_sharp
#print axioms Mixes.Bipyramid.key_identity
#print axioms Mixes.Bipyramid.levels
#print axioms Mixes.Bipyramid.reduce_c
#print axioms Mixes.Bipyramid.reduce_c2
#print axioms Mixes.Bipyramid.completelyMixable_of_tendsto
#print axioms Mixes.Bipyramid.reduce_a
#check @Mixes.SymmCor.partA_space
#check @Mixes.SymmCor.partB_five
#print axioms Mixes.SymmCor.partA
#print axioms Mixes.SymmCor.partA_plane
#print axioms Mixes.SymmCor.partA_space
#print axioms Mixes.SymmCor.partB
#print axioms Mixes.SymmCor.partB_four
#print axioms Mixes.SymmCor.partB_five
#print axioms Mixes.SymmCor.ball_core
#print axioms Mixes.SymmCor.dodecahedron
#print axioms Mixes.SymmCor.icosahedron
#print axioms Mixes.SymmCor.cell24
#print axioms Mixes.SymmCor.cell600
#print axioms Mixes.SymmCor.cell120
#print axioms Mixes.SymmCor.partD
#print axioms Mixes.SymmCor.no_eigen_one_plane
#print axioms Mixes.SymmCor.partD_plane
#check @Mixes.seg_mix
#check @Mixes.lem18
#check @Mixes.prop24
#print axioms Mixes.seg_mix
#print axioms Mixes.seg_mix_density
#print axioms Mixes.lem17
#print axioms Mixes.lem18
#print axioms Mixes.prop24
#print axioms Mixes.P24.cases_exclusive
#check @Mixes.JointLemmas.slab_lemma
#check @Mixes.JointLemmas.split_lemma
#print axioms Mixes.JointLemmas.slab_lemma
#print axioms Mixes.JointLemmas.slab_lemma_exists
#print axioms Mixes.JointLemmas.recog_pos
#print axioms Mixes.JointLemmas.recog_zero
#print axioms Mixes.JointLemmas.pairs_lemma
#print axioms Mixes.JointLemmas.pairs_lemma_F
#print axioms Mixes.JointLemmas.split_lemma
#check @Mixes.JointSplit.lem25
#check @Mixes.JointSplit.prop26
#print axioms Mixes.JointSplit.lem25
#print axioms Mixes.JointSplit.three_groups_bound
#print axioms Mixes.JointSplit.prop26_kappa
#print axioms Mixes.JointSplit.prop26_i
#print axioms Mixes.JointSplit.prop26_ii
#print axioms Mixes.JointSplit.prop26_iii
#print axioms Mixes.JointSplit.prop26
#check @Mixes.Room.fibre_triple
#check @Mixes.Room.room
#check @Mixes.Room.planar_asym
#check @Mixes.Room.completelyMixable_unif_iff
#check @Mixes.Room.symm_robust
#print axioms Mixes.Room.fibre_core
#print axioms Mixes.Room.fibre_triple
#print axioms Mixes.Room.reflect_mem_of_asymLE
#print axioms Mixes.Room.room
#print axioms Mixes.Room.planar_asym
#print axioms Mixes.Room.room_planar_three
#print axioms Mixes.Room.completelyMixable_iff_tuples
#print axioms Mixes.Room.completelyMixable_unif_iff
#print axioms Mixes.Room.symm_room
#print axioms Mixes.Room.symm_robust
#check @Mixes.ConeMix.cone_sufficiency
#check @Mixes.ConeMix.simplex_completelyMixable_iff
#check @Mixes.ConeMix.pyramid_completelyMixable_iff
#check @Mixes.ConeMix.tetrahedron_completelyMixable
#print axioms Mixes.ConeMix.cone_sufficiency
#print axioms Mixes.ConeMix.cone_scalingProperty
#print axioms Mixes.ConeMix.simplex_scalingPropertySet
#print axioms Mixes.ConeMix.simplex_jointlyMixable_iff
#print axioms Mixes.ConeMix.simplex_completelyMixable_iff
#print axioms Mixes.ConeMix.simplex_necessity
#print axioms Mixes.ConeMix.scalingProperty_Icc
#print axioms Mixes.ConeMix.scalingProperty_cube
#print axioms Mixes.ConeMix.pyramid_scalingPropertySet
#print axioms Mixes.ConeMix.pyramid_completelyMixable_iff
#print axioms Mixes.ConeMix.pyramid_necessity
#print axioms Mixes.ConeMix.khintchine
#print axioms Mixes.ConeMix.tetra_completelyMixable
#print axioms Mixes.ConeMix.tetrahedron_completelyMixable
#print axioms Mixes.ConeMix.completelyMixable_image_equiv
#check @Mixes.Ball.ball_jointlyMixable_iff
#check @Mixes.Ball.prop52
#print axioms Mixes.Ball.ball_scalingProperty
#print axioms Mixes.Ball.ball_scalingPropertySet
#print axioms Mixes.Ball.ball_jointlyMixable_iff
#print axioms Mixes.Ball.ball_completelyMixable
#print axioms Mixes.Ball.polyVec_spec
#print axioms Mixes.Ball.lemma50
#print axioms Mixes.Ball.prop52_necessity
#print axioms Mixes.Ball.prop52_sufficiency
#print axioms Mixes.Ball.prop52
#print axioms Mixes.Ball.completelyMixable_of_isRotInv
#print axioms Mixes.BallBridge.circCone_completelyMixable_iff
#print axioms Mixes.BallBridge.partA_plane
#print axioms Mixes.BallBridge.partA_space

-- Mixes: Large.lean (Lemmas 101, 102, 111, Props 106, 116, Remark 85, Cors 105, 114, 115)
#print axioms Mixes.Large.lemma101
#print axioms Mixes.Large.lemma102
#print axioms Mixes.Large.lemma111a
#print axioms Mixes.Large.lemma111a_of
#print axioms Mixes.Large.lemma111b
#print axioms Mixes.Large.lemma111c
#print axioms Mixes.Large.centroid_support
#print axioms Mixes.Large.asymLE_cent
#print axioms Mixes.Large.neg_sub_cent_mem
#print axioms Mixes.Large.prop106
#print axioms Mixes.Large.prop106_unique
#print axioms Mixes.Large.prop116
#print axioms Mixes.Large.relEntropy_normalised
#print axioms Mixes.Large.cor105
#print axioms Mixes.Large.cor114
#print axioms Mixes.Large.cor115
#check @Mixes.Large.cor105

-- Mixes: ClassK.lean (Lemma 59 corrected, Def 60, Thm 61)
#print axioms Mixes.ClassK.transport
#print axioms Mixes.ClassK.unifSet_joinSet
#print axioms Mixes.ClassK.join_scalingProperty
#print axioms Mixes.ClassK.join_points_not_scaling
#print axioms Mixes.ClassK.classK_scalingProperty
#print axioms Mixes.ClassK.thm51Ball
#print axioms Mixes.ClassK.classK_scalingProperty'
#print axioms Mixes.ClassK.classK_jointlyMixable'
#print axioms Mixes.ClassK.classK_completelyMixable'
#print axioms Mixes.ClassK.cone_completelyMixable_iff'
#check @Mixes.ClassK.join_points_not_scaling

-- Mixes: Scaled.lean, ScaledB.lean (Section 20; Thms 73, 75, 79, Cors 74, 77, 80, 84, Remark 81)
#print axioms Mixes.Scaled.completelyMixable_pieceP
#print axioms Mixes.Scaled.thm73a
#print axioms Mixes.Scaled.thm73b
#print axioms Mixes.Scaled.cor84a
#print axioms Mixes.Scaled.cor84c
#print axioms Mixes.Scaled.cor84d
#print axioms Mixes.Scaled.cor84e
#print axioms Mixes.Scaled.lemma82_identity
#print axioms Mixes.Scaled.thm83_fibre_max
#print axioms Mixes.ScaledB.thm75
#print axioms Mixes.ScaledB.thm75_beta
#print axioms Mixes.ScaledB.cor77
#print axioms Mixes.ScaledB.thm79
#print axioms Mixes.ScaledB.thm79_completelyMixable
#print axioms Mixes.ScaledB.KPlus.join
#print axioms Mixes.ScaledB.cor74a
#print axioms Mixes.ScaledB.cor74a_sharp
#print axioms Mixes.ScaledB.cor74b
#print axioms Mixes.ScaledB.cor80a
#print axioms Mixes.ScaledB.cor80b
#print axioms Mixes.ScaledB.cor80b_pentagon
#print axioms Mixes.ScaledB.completelyMixable_add_add
#print axioms Mixes.ScaledB.rem81_cyclic
#print axioms Mixes.ScaledB.rem81_pentagon

-- Mixes: Decomp.lean, ConcaveMix.lean, Peel.lean (Lemma 33, Thms 34, 35, 36, Cor 39)
#print axioms Mixes.Decomp.decomp
#print axioms Mixes.Decomp.piU_eq_left
#print axioms Mixes.ConcaveMix.thm36
#print axioms Mixes.ConcaveMix.H36_of
#print axioms Mixes.ConcaveMix.pconc'
#print axioms Mixes.ConcaveMix.cor39
#print axioms Mixes.Peel.lemma33_continuousOn
#print axioms Mixes.Peel.lemma33_deriv_x
#print axioms Mixes.Peel.lemma33_deriv_U
#print axioms Mixes.Peel.lemma33_differentiable
#print axioms Mixes.Peel.lemma33_shape
#print axioms Mixes.Peel.thm34_exists_unique
#print axioms Mixes.Peel.thm34_C1
#print axioms Mixes.Peel.thm34_a
#print axioms Mixes.Peel.thm34_b
#print axioms Mixes.Peel.thm34_c_left
#print axioms Mixes.Peel.thm34_c_right
#print axioms Mixes.Peel.thm34_d
#print axioms Mixes.Peel.thm35
#print axioms Mixes.Peel.cor39
#print axioms Mixes.Peel.cor39_completelyMixable
#print axioms Mixes.Peel.QCDensity.peel34
#check @Mixes.Peel.cor39_completelyMixable

-- Mixes: Theorem27.lean (Theorem 27, Corollaries 28, 30, 44, 45; Theorem 73(b))
#print axioms Mixes.Theorem27.necessity
#print axioms Mixes.Theorem27.thm27
#print axioms Mixes.Theorem27.thm27_concave
#print axioms Mixes.Theorem27.dclass_of_concave
#print axioms Mixes.Theorem27.cor_cm
#print axioms Mixes.Theorem27.cor_cm_concave
#print axioms Mixes.Theorem27.cor30
#print axioms Mixes.Theorem27.exists_unif_rep
#print axioms Mixes.Theorem27.scaled_unif_rep
#print axioms Mixes.Theorem27.thm27Frustum
#print axioms Mixes.Theorem27.thm27Frustum_all
#print axioms Mixes.Theorem27.simplex_jointlyMixable_iff'
#print axioms Mixes.Theorem27.simplex_completelyMixable_iff'
#print axioms Mixes.Theorem27.pyramid_completelyMixable_iff'
#print axioms Mixes.Theorem27.thm73b_of_thm27
#print axioms Mixes.Theorem27.procMix_spec
#print axioms Mixes.Theorem27.pieceMix_spec
#print axioms Mixes.Theorem27.exists_pieces
#check @Mixes.Theorem27.thm27_concave

-- Mixes: Unconditional.lean (Corollary 58, Theorem 61 without hypotheses)
#print axioms Mixes.Unconditional.pyramid_completelyMixable_iff
#print axioms Mixes.Unconditional.circCone_completelyMixable_iff
#print axioms Mixes.Unconditional.classK_scalingProperty
#print axioms Mixes.Unconditional.classK_jointlyMixable
#print axioms Mixes.Unconditional.classK_completelyMixable
#print axioms Mixes.Unconditional.cone_completelyMixable_iff
#check @Mixes.Unconditional.classK_completelyMixable

-- Mixes: Sphere.lean (uniqueness on the sphere; Lemma 50, Proposition 52 without hypotheses)
#print axioms Mixes.Sphere.sphereUniqueness
#print axioms Mixes.Sphere.polar
#print axioms Mixes.Sphere.lemma50
#print axioms Mixes.Sphere.frame_law_scaled
#print axioms Mixes.Sphere.prop52_sufficiency
#print axioms Mixes.Sphere.prop52
#print axioms Mixes.Sphere.completelyMixable_of_isRotInv
#check @Mixes.Sphere.prop52

-- Mixes: Bridges.lean (Thm 67, Section 20, Lemma 89, Cor 64, Cor 99, Cor j:cor:finite)
#print axioms Mixes.Bridges.qcDensity_rpow
#print axioms Mixes.Bridges.peelingProps_of_sol
#print axioms Mixes.Bridges.pconc
#print axioms Mixes.Bridges.cor_monotone_a
#print axioms Mixes.Bridges.cor_monotone_b
#print axioms Mixes.Bridges.cor_monotone_b_of_scaling
#print axioms Mixes.Bridges.asymLE_centroid
#print axioms Mixes.Bridges.room
#print axioms Mixes.Bridges.partA
#print axioms Mixes.Bridges.dodecahedron
#print axioms Mixes.Bridges.icosahedron
#print axioms Mixes.Bridges.cell24
#print axioms Mixes.Bridges.cell600
#print axioms Mixes.Bridges.cell120
#print axioms Mixes.Bridges.scalingProperty_of_decomp
#print axioms Mixes.Bridges.scalingProperty_rpow
#print axioms Mixes.Bridges.cor74a
#print axioms Mixes.Bridges.scalingProperty_levLaw
#print axioms Mixes.Bridges.scalingProperty_segment
#print axioms Mixes.Bridges.thm75
#print axioms Mixes.Bridges.cor77
#print axioms Mixes.Bridges.thm79
#print axioms Mixes.Bridges.thm79_completelyMixable
#print axioms Mixes.Bridges.cor80a
#print axioms Mixes.Bridges.cor80b
#print axioms Mixes.Bridges.cor74b
#print axioms Mixes.Bridges.procMix_segMix
#print axioms Mixes.Bridges.pieceMix_segMix
#check @Mixes.Bridges.pconc

-- Mixes: ScaledC.lean (Lemma 82, Theorem 83, Corollary 84(b))
#print axioms Mixes.ScaledC.levels82
#print axioms Mixes.ScaledC.levels82_paper
#print axioms Mixes.ScaledC.levelMix82_half
#print axioms Mixes.ScaledC.antitoneOn_of_even_concave
#print axioms Mixes.ScaledC.ac_of_concave
#print axioms Mixes.ScaledC.levelDist_eq_symNu
#print axioms Mixes.ScaledC.thm83_three
#print axioms Mixes.ScaledC.thm83_two
#print axioms Mixes.ScaledC.thm83
#print axioms Mixes.ScaledC.condP_of_tail
#print axioms Mixes.ScaledC.cor84b_cond
#print axioms Mixes.ScaledC.cor84b
#print axioms Mixes.ScaledC.frustumSet_eq_hull
#print axioms Mixes.ScaledC.unifSet_image_affineEquiv
#print axioms Mixes.ScaledC.KPlus_frustum
#check @Mixes.ScaledC.thm83

-- Mixes: Robust.lean (kernel argument, Prop 106 uniqueness, Def 90, core of Thm 91, Cor 93)
#print axioms Mixes.Robust.pexider_local
#print axioms Mixes.Robust.glue_affine
#print axioms Mixes.Robust.kernelAffine_of_room
#print axioms Mixes.Robust.kernelAffine_of_asym
#print axioms Mixes.Robust.prop106_unique_of_asym
#print axioms Mixes.Robust.spectral_gap
#print axioms Mixes.Robust.solve_of_gap
#print axioms Mixes.Robust.linear_correction
#print axioms Mixes.Robust.robust_of_symm
#print axioms Mixes.Robust.stable_of_thm91
#print axioms Mixes.Robust.cor93a
#print axioms Mixes.Robust.cor93b
#print axioms Mixes.Robust.ball_robust'
#print axioms Mixes.Robust.cor93c'
#check @Mixes.Robust.prop106_unique_of_asym

-- Mixes: Masking.lean, Markov.lean (Props 108, 109, 117, 123; Lemma 119; Thms 120, 121; Cor 122)
#print axioms Mixes.tv_translate_le
#print axioms Mixes.prop109_a
#print axioms Mixes.prop109_b
#print axioms Mixes.prop109_c_hyp
#print axioms Mixes.prop109_c_cyclic
#print axioms Mixes.prop117_a
#print axioms Mixes.prop117_b
#print axioms Mixes.volume_sdiff_tr_le_proj_dir
#print axioms Mixes.tfun_le_proj_dir
#print axioms Mixes.prop117_thm113
#print axioms Mixes.prop_price
#print axioms Mixes.prop_price_tv
#print axioms Mixes.lem_mean
#print axioms Mixes.lem_mean_markov
#print axioms Mixes.doeblin_unique
#print axioms Mixes.cesaro_limit_invariant
#print axioms Mixes.exists_invariant_of_feller
#print axioms Mixes.markov_stationary
#print axioms Mixes.thm120_a
#print axioms Mixes.thm120_b
#print axioms Mixes.thm121_a
#print axioms Mixes.thm121_b
#print axioms Mixes.cor_ball_invariant
#print axioms Mixes.cor_ball
#check @Mixes.cor_ball

-- Mixes: Poly.lean (Theorem 95 in steps, Corollary 96)
#print axioms Mixes.Poly.cor96a_ge_eight
#print axioms Mixes.Poly.cor96a_seven
#print axioms Mixes.Poly.cor96b_four
#print axioms Mixes.Poly.cor96b_four_eight
#print axioms Mixes.Poly.cor96b_five
#print axioms Mixes.Poly.completelyMixable_of_rest
#print axioms Mixes.Poly.completelyMixable_of_densities
#print axioms Mixes.Poly.abs_integral_antitone_mul_cos_le
#print axioms Mixes.Poly.neumann
#print axioms Mixes.Poly.pointwise_of_cond21
#print axioms Mixes.Poly.all_of_three_four_five
#print axioms Mixes.Poly.cor96d
#print axioms Mixes.Poly.marginal_withDensity_sum
#print axioms Mixes.Poly.corner_marginal
#check @Mixes.Poly.cor96d

-- Mixes: Quad.lean (Proposition 87)
#print axioms Mixes.Quad.prop87_quad
#print axioms Mixes.Quad.rep_all
#print axioms Mixes.Quad.hull_eq
#print axioms Mixes.Quad.IsQuad.rep
#print axioms Mixes.Quad.sliced_of_body
#print axioms Mixes.Quad.isCompleteMix_map
#print axioms Mixes.Quad.QuadBody.prop87
#print axioms Mixes.Quad.BentBody.no_sliced
#print axioms Mixes.Quad.Quad3.prop87
#check @Mixes.Quad.prop87_quad

-- Mixes: LLT.lean (Lemma 103; steps of Theorem 104)
#print axioms Mixes.LLT.convPow_eq_inv
#print axioms Mixes.LLT.hatC_sq
#print axioms Mixes.LLT.fourier_convPow
#print axioms Mixes.LLT.hatC_taylor
#print axioms Mixes.LLT.llt_bound
#print axioms Mixes.LLT.tendsto_epsB
#print axioms Mixes.LLT.lemma103_eps
#print axioms Mixes.LLT.lemma103_delta
#print axioms Mixes.LLT.condMeas_marg
#print axioms Mixes.LLT.completelyMixable_of_marg
#print axioms Mixes.LLT.ratio_bound
#print axioms Mixes.LLT.lip_log_convPow
#print axioms Mixes.LLT.vol_diff_translate
#print axioms Mixes.LLT.l1_modulus
#check @Mixes.LLT.lemma103_eps

-- Mixes: Thm113.lean (Lemma 112)
#print axioms Mixes.Thm113.InH.of_InG
#print axioms Mixes.Thm113.InH.varF_le
#print axioms Mixes.Thm113.InH.varF_ge
#print axioms Mixes.Thm113.llt_eps
#print axioms Mixes.Thm113.llt_delta
#print axioms Mixes.Thm113.llt_near
#print axioms Mixes.Thm113.gauss0_ge
#check @Mixes.Thm113.llt_eps

-- Mixes: KPlusIncl.lean (K ⊂ K+)
#print axioms Mixes.KPlusIncl.reg_and_kPlus
#print axioms Mixes.KPlusIncl.inK_subset_kPlus
#print axioms Mixes.KPlusIncl.classK_scaling_of_kPlus
#print axioms Mixes.KPlusIncl.classK_completelyMixable_of_kPlus
#print axioms Mixes.KPlusIncl.KPlus.transfer
#check @Mixes.KPlusIncl.inK_subset_kPlus

-- Mixes: Reduce.lean (Proposition 71(a))
#print axioms Mixes.Reduce.completelyMixable_of_tendsto
#print axioms Mixes.Reduce.tendsto_unifP
#print axioms Mixes.Reduce.mem_of_ball_subset
#print axioms Mixes.Reduce.ae_eventually_mem_iff
#print axioms Mixes.Reduce.reduce_a
#print axioms Mixes.Reduce.exists_polytopes_tendsto
#print axioms Mixes.Reduce.op5_iff_polytopes
#check @Mixes.Reduce.op5_iff_polytopes

-- Mixes: Bipyr.lean (Theorem 70, Corollary 99(b))
#print axioms Mixes.Bipyr.starr_iff
#print axioms Mixes.Bipyr.thm70_three
#print axioms Mixes.Bipyr.thm70
#print axioms Mixes.Bipyr.starr_of_affine
#print axioms Mixes.Bipyr.thm70_affine
#print axioms Mixes.Bipyr.thm70_bipyramid
#print axioms Mixes.Bipyr.thm70_image
#print axioms Mixes.Bipyr.bipyr_ellipsoid
#print axioms Mixes.Bipyr.bipyr_parallelotope
#print axioms Mixes.Bipyr.octahedron
#print axioms Mixes.Bipyr.dcone_completelyMixable
#print axioms Mixes.Bipyr.cor99b
#print axioms Mixes.Bipyr.cor99b_four
#print axioms Mixes.Bipyr.cor99b_five
#check @Mixes.Bipyr.bipyr_ellipsoid

-- Mixes: Proj.lean (Corollary 68)
#print axioms Mixes.Proj.concave_extend
#print axioms Mixes.Proj.pconc_Ioo
#print axioms Mixes.Proj.exists_chart
#print axioms Mixes.Proj.map_restrict_eq
#print axioms Mixes.Proj.cor68
#print axioms Mixes.Proj.cor68_cone
#check @Mixes.Proj.cor68

-- Mixes: Flat.lean (Corollary 84(f))
#print axioms Mixes.Flat.bodyK_prof
#print axioms Mixes.Flat.flat_mixable
#print axioms Mixes.Flat.table_conditions
#print axioms Mixes.Flat.cor84f
#print axioms Mixes.Flat.cor84f_named
#check @Mixes.Flat.cor84f_named

-- Mixes: LLTB.lean (Theorem 104, Corollary 105)
#print axioms Mixes.LLTB.thm104T
#print axioms Mixes.LLTB.fourierGapJohn
#print axioms Mixes.LLTB.cor105_full
#print axioms Mixes.LLTB.thm104_centred
#print axioms Mixes.LLTB.cm_of_body
#check @Mixes.LLTB.cor105_full

-- Mixes: Thm113B.lean (Theorem 113, Corollaries 114, 115, Theorem 121(a); Tychonoff fixed point hypothesis)
#print axioms Mixes.Thm113B.thm113
#print axioms Mixes.Thm113B.thm113Sym
#print axioms Mixes.Thm113B.cor114'
#print axioms Mixes.Thm113B.cor115'
#print axioms Mixes.Thm113B.thm121_a'
#check @Mixes.Thm113B.thm113

-- Mixes: PolyB.lean (Theorem 95, Corollary 96(d))
#print axioms Mixes.PolyB.thm95
#print axioms Mixes.PolyB.thm95_pointwise
#print axioms Mixes.PolyB.thm95_of_phi
#print axioms Mixes.PolyB.exists_phi
#print axioms Mixes.PolyB.mode_solve
#print axioms Mixes.PolyB.cor96d_poly
#print axioms Mixes.PolyB.cor96d_poly_iff
#print axioms Mixes.PolyB.completelyMixable_two_iff_even
#print axioms Mixes.PolyB.volume_poly
#print axioms Mixes.PolyB.arc_integral
#print axioms Mixes.PolyB.fourier_ae
#print axioms Mixes.PolyB.norm_Top_le
#print axioms Mixes.PolyB.norm_proj_nu_le
#print axioms Mixes.PolyB.cm_self
#check @Mixes.PolyB.cor96d_poly

-- Mixes: RobustB.lean (Theorem 91, Corollary 93; Hilbert-Schmidt compactness as hypothesis)
#print axioms Mixes.RobustB.thm91_centred
#print axioms Mixes.RobustB.thm91
#print axioms Mixes.RobustB.kernelHyp_inner
#print axioms Mixes.RobustB.kernelHyp_prod
#print axioms Mixes.RobustB.cor93a
#print axioms Mixes.RobustB.cor93b
#print axioms Mixes.RobustB.cor93c
#print axioms Mixes.RobustB.abstract_main
#print axioms Mixes.RobustB.construct
#check @Mixes.RobustB.thm91
#check @Mixes.RobustB.cor93c
#print axioms Mixes.AsymWindow.lemTilt
#print axioms Mixes.AsymWindow.tiltKH_spec
#print axioms Mixes.AsymWindow.measurable_tiltKH
#print axioms Mixes.AsymWindow.eq_affine
#print axioms Mixes.AsymWindow.propWindow
#print axioms Mixes.AsymWindow.propWindowReal
#print axioms Mixes.AsymWindow.propWindowThree
#print axioms Mixes.AsymWindow.window_box
#print axioms Mixes.AsymThm.lem_conc_a
#print axioms Mixes.AsymThm.lem_conc_b
#print axioms Mixes.AsymThm.thm_window_d1_proved
#print axioms Mixes.AsymThm.thm_window_one_proved
#print axioms Mixes.AsymThm.cor_interval_proved
#print axioms Mixes.AsymThm.cor_interval_n_proved
#print axioms Mixes.AsymThm.cor_interval_density_proved
#print axioms Mixes.Steinitz.steinitz_normed
#print axioms Mixes.Steinitz.steinitz_nonneg
#print axioms Mixes.Steinitz.lem_conc_c_uncond
#print axioms Mixes.Steinitz.couplingBound_all
#print axioms Mixes.Steinitz.thm_window_all
#print axioms Mixes.Steinitz.not_H_steinitz
#print axioms Mixes.AsymBridge.thm_general_b
#print axioms Mixes.AsymBridge.thm_general_mix_b
#print axioms Mixes.AsymBridge.cor_order_b
#print axioms Mixes.AsymBridge.cor_body_b
#print axioms Mixes.AsymBridge.thm_hetero_strong_b
#print axioms Mixes.AsymBridge.thm_hetero_b
#print axioms Mixes.AsymBridge.thm_hetero_jointlyMixable_b
#print axioms Mixes.AsymBridge.cor_hetero_b
#print axioms Mixes.AsymBridge.cor_hetero_jointlyMixable_b
#print axioms Mixes.AsymBridge.cor_hetero_n_b
#print axioms Mixes.AsymBridge.prop_complete_b
#print axioms Mixes.AsymBridge.prop_complete_dirac_b
#print axioms Mixes.AsymBridge.four_uniform_jointlyMixable_b
#print axioms Mixes.AsymBridge.cor_repeat_b
#print axioms Mixes.AsymBridge.cor_three_b
#print axioms Mixes.AsymBridge.cor_three_mixable_b
#print axioms Mixes.AsymBridge.cor_three_a_b
#print axioms Mixes.AsymBridge.cor_three_b_b
#print axioms Mixes.AsymBridge.cor_three_c_b
#print axioms Mixes.AsymBridge.prop_three_b
#print axioms Mixes.AsymBridge.rem_three_b
#print axioms Mixes.AsymBridge.cxCond_of_SL_b
#print axioms Mixes.AsymBridge.cx_F1_F2_b
#print axioms Mixes.AsymBridge.cor_alln_mixable_b
#print axioms Mixes.AsymBridge.threshold_unimodal_b
#print axioms Mixes.AsymBridge.normIneqs_of_SL_b
#print axioms Mixes.AsymBridge.thm_unimodal_norm_b
#print axioms Mixes.AsymBridge.cor_alln_norm_b
#print axioms Mixes.AsymBridge.not_H_conc_a
#print axioms Mixes.ConvSq.convSq
#print axioms Mixes.ConvSq.cor_repeat_cs
#print axioms Mixes.TwoStepBorel.twoStepBorel
#print axioms Mixes.TwoStepBorel.KT_spec
#print axioms Mixes.TwoStepBorel.prop_three_tb
#print axioms Mixes.StopLoss.stoploss_cx
#print axioms Mixes.StopLoss.atom_cx_uncond
#print axioms Mixes.StopLoss.cor_least_explicit_uncond
#print axioms Mixes.StopLoss.cor_least_exists_uncond
#print axioms Mixes.NormAtom.peak
#print axioms Mixes.NormAtom.peak_interval
#print axioms Mixes.NormAtom.peak_completelyMixable
#print axioms Mixes.NormAtom.count_lemma
#print axioms Mixes.NormAtom.count_lemma_reflect
#print axioms Mixes.NormAtom.atom_sufficiency
#print axioms Mixes.NormAtom.atom_necessity
#print axioms Mixes.NormAtom.atom_completelyMixable_iff
#print axioms Mixes.NormAtom.atom_stopLoss
#print axioms Mixes.NormAtom.cor_least_iff
#print axioms Mixes.ProjMain.pj_thm_main_uncond
#print axioms Mixes.ProjMain.pj_thm_main_proj_uncond
#print axioms Mixes.ProjMain.pj_thm_main_analytic_uncond
#print axioms Mixes.ProjMain.pj_cor_confine_uncond
#print axioms Mixes.ProjMain.rem_product
#print axioms Mixes.LatticeBridge.binom_eq
#print axioms Mixes.LatticeBridge.lem_count
#print axioms Mixes.LatticeBridge.thm_pb
#print axioms Mixes.LatticeBridge.prop_three
#print axioms Mixes.LatticeBridge.large_a_uncond
#print axioms Mixes.LatticeBridge.large_b_uncond
#print axioms Mixes.LatticeBridge.large_eventually_uncond
#print axioms Mixes.LatticeBridge.large_c_two_uncond
#print axioms Mixes.LatticeBridge.binomial_a_uncond
#print axioms Mixes.LatticeBridge.binomial_c_uncond
#print axioms Mixes.LatticeBridge.remark_necessary_uncond
#print axioms Mixes.LatticeLarge.large_c_int
#print axioms Mixes.LatticeLarge.binomial_b_add
#print axioms Mixes.LatticeLarge.binomial_b_N0
#print axioms Mixes.LatticeLarge.shapes
#print axioms Mixes.LatticeBasic.count_iff_fintype
#print axioms Mixes.LatticeBasic.binom_completelyMixable
#print axioms Mixes.LatticeBasic.binom2_cm_iff
#print axioms Mixes.LatticeBasic.ops_a
#print axioms Mixes.LatticeBasic.ops_b
#print axioms Mixes.LatticeBasic.ops_c
#print axioms Mixes.LatticeBasic.three_cm_iff
#print axioms Mixes.ProjLemmas.three_a
#print axioms Mixes.ProjLemmas.three_b
#print axioms Mixes.ProjLemmas.ex_not_jointlyMixable
#print axioms Mixes.ProjLemmas.ex_map_jointlyMixable
#print axioms Mixes.ProjLemmas.gadget_a
#print axioms Mixes.ProjLemmas.gadget_b
#print axioms Mixes.Remarks14.prop_generic_a_mix
#print axioms Mixes.Remarks14.prop_generic_b
#print axioms Mixes.Remarks14.prop_generic_c
#print axioms Mixes.Remarks14.jointlyMixable_iff_exists_cE
#print axioms Mixes.Remarks14.isArchimedesMeasure_sphUnif
#print axioms Mixes.Remarks14.tau_exchange
#print axioms Mixes.Remarks14.rho_exchange
#print axioms Mixes.Remarks14.S_no_jump
#print axioms Mixes.Remarks14.collinear_of_tight
#print axioms Mixes.Remarks14.disc_polygon_fails
#print axioms Mixes.Remarks14.chord_jointMix
#print axioms Mixes.Archimedes.archimedes
#print axioms Mixes.Archimedes.sphUnif_map_inner_uncond
#print axioms Mixes.Archimedes.isArchimedesMeasure_sphUnif_uncond
#print axioms Mixes.AsymRate.thm_general_rate
#print axioms Mixes.AsymRate.thm_general_rate_of
#print axioms Mixes.AsymRate.cor_order_rate
#print axioms Mixes.BorelSelect.exists_selection
#print axioms Mixes.BorelSelect.borelSelection_pi
#print axioms Mixes.BorelSelect.thm120_a_uncond
#print axioms Mixes.BorelSelect.thm120_uncond
#print axioms Mixes.Combined.res18
#print axioms Mixes.Combined.res43
#print axioms Mixes.Combined.res45
#print axioms Mixes.Combined.res56
#print axioms Mixes.Combined.res57
#print axioms Mixes.Combined.res58
#print axioms Mixes.Combined.res59
#print axioms Mixes.Combined.res79
#print axioms Mixes.Combined.res86
#print axioms Mixes.PrekopaLeindler.bm1
#print axioms Mixes.PrekopaLeindler.pl1
#print axioms Mixes.PrekopaLeindler.prekopa_leindler
#print axioms Mixes.PrekopaLeindler.prekopa_leindler_complex
#print axioms Mixes.PrekopaLeindler.brunn_minkowski
#print axioms Mixes.PrekopaLeindler.plHyp
#print axioms Mixes.PrekopaLeindler.brunnSections
#print axioms Mixes.PrekopaLeindler.cor68_pl
#print axioms Mixes.PrekopaLeindler.thm95_pl
#print axioms Mixes.PrekopaLeindler.cor96d_poly_pl
#print axioms Mixes.Brunn74.law_Ioo
#print axioms Mixes.Brunn74.affine_of_Ioo
#print axioms Mixes.Brunn74.exists_brunn
#print axioms Mixes.Brunn74.cor74b_brunn
#print axioms Mixes.Brunn74.cor74b_bridges
