import Mixes.Pieces

/-!
# The layer-cake decomposition of a peeled unimodal density (Theorem 35, `c:thm:decomp`)

For `0 ≤ U < f(μ)` the measure
`π_U = 1_{[A(U),B(U)]} dx + (r² - ℓ²)⁺/(2ℓ) δ_{A(U)} + (ℓ² - r²)⁺/(2r) δ_{B(U)}`
(`ℓ = μ - A(U)`, `r = B(U) - μ`) is `piU μ (A U) (B U)`.

* `decomp`: `∫_0^{f(μ)} π_U dU = f(x) dx` on `[0,1]`, as an equality of measures
  (`Measure.bind` of the kernel `U ↦ π_U` over Lebesgue measure on `(0, f μ)`);
  `decomp_lintegral`: the same tested against measurable `φ ≥ 0`.
* `piU_eq_left`, `piU_eq_right`: `π_U = W(U) •` (image of `P_{β(U)}` under the affine map).
* `piU_univ`, `piU_mean`: total mass `W(U)` and mean `μ`.
* `lintegral_W`, `lintegral_W_eq_one`: `W` is a probability density on `(0, f μ)`.

The conclusions of Theorem 34 that are used are hypotheses, bundled in `Peel34`; Theorem 34 is
proved separately. The proof follows the paper, with the chain rule `(c:eq:chain)` replaced by
two facts about the Stieltjes measure `dA` of a function `A` continuous on `[0, u]`: its image
under `A` is Lebesgue measure (`map_measure_Ioc`), and integration by parts via Tonelli
(`lintegral_sub_dA`). The identity is checked on the sets `(-∞, x]`, `x ≤ μ`, which see only the
left end (`left_cdf`), and on `[y, ∞)`, `y ≥ μ`, which see only the right end (by reflection).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace Mixes.Decomp

/-! ### Stieltjes calculus for a monotone function continuous on an interval -/

/-- The image of `dA` on `(a, u]` under `A` is Lebesgue measure on `(A a, A u]`, for `A`
continuous on `[a, u]`. -/
lemma map_measure_Ioc (A : StieltjesFunction ℝ) {a u : ℝ} (hau : a ≤ u)
    (hA : ContinuousOn A (Icc a u)) :
    (A.measure.restrict (Ioc a u)).map A = volume.restrict (Ioc (A a) (A u)) := by
  have hAm : Measurable A := A.mono.measurable
  have : IsFiniteMeasure (A.measure.restrict (Ioc a u)) :=
    isFiniteMeasure_restrict.2 (by rw [A.measure_Ioc]; exact ENNReal.ofReal_ne_top)
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply hAm measurableSet_Iic, Measure.restrict_apply (hAm measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt (A u) y with hy | hy
  · have h1 : A ⁻¹' Iic y ∩ Ioc a u = Ioc a u := by
      refine inter_eq_right.2 fun U hU => ?_
      exact (A.mono hU.2).trans hy
    have h2 : Iic y ∩ Ioc (A a) (A u) = Ioc (A a) (A u) :=
      inter_eq_right.2 fun t ht => ht.2.trans hy
    rw [h1, h2, A.measure_Ioc, Real.volume_Ioc]
  rcases lt_or_ge y (A a) with hy' | hy'
  · have h1 : A ⁻¹' Iic y ∩ Ioc a u = ∅ := by
      refine eq_empty_of_forall_notMem fun U hU => ?_
      exact absurd ((A.mono hU.2.1.le).trans hU.1) (not_le.2 hy')
    have h2 : Iic y ∩ Ioc (A a) (A u) = ∅ := by
      refine eq_empty_of_forall_notMem fun t ht => ?_
      exact absurd (ht.2.1.trans_le ht.1) (not_lt.2 hy'.le)
    rw [h1, h2, measure_empty, measure_empty]
  -- the last level `v ≤ u` with `A v ≤ y`
  set S := {U ∈ Icc a u | A U ≤ y} with hS
  have hSc : IsClosed S := hA.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hau⟩, hy'⟩
  have hSb : BddAbove S := ⟨u, fun U hU => hU.1.2⟩
  set v := sSup S with hv
  have hvS : v ∈ S := hSc.csSup_mem hSne hSb
  have hAv : A v = y := by
    obtain ⟨w, hw, hwy⟩ := intermediate_value_Icc hvS.1.2 (hA.mono (Icc_subset_Icc hvS.1.1 le_rfl))
      ⟨hvS.2, hy.le⟩
    have hwS : w ∈ S := ⟨⟨hvS.1.1.trans hw.1, hw.2⟩, hwy.le⟩
    have : w = v := le_antisymm (le_csSup hSb hwS) hw.1
    rw [← this, hwy]
  have h1 : A ⁻¹' Iic y ∩ Ioc a u = Ioc a v := by
    ext U
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hU, haU, hUu⟩
      exact ⟨haU, le_csSup hSb ⟨⟨haU.le, hUu⟩, hU⟩⟩
    · rintro ⟨haU, hUv⟩
      exact ⟨(A.mono hUv).trans hAv.le, haU, hUv.trans hvS.1.2⟩
  have h2 : Iic y ∩ Ioc (A a) (A u) = Ioc (A a) y := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', h.trans hy.le⟩
  rw [h1, h2, A.measure_Ioc, Real.volume_Ioc, hAv]

/-- Integration by parts in the form `∫_{(a,u]} (U - a) dA(U) = ∫_a^u (A u - A s) ds`. -/
lemma lintegral_sub_dA (A : StieltjesFunction ℝ) (a u : ℝ) :
    ∫⁻ U in Ioc a u, ENNReal.ofReal (U - a) ∂A.measure =
      ∫⁻ s in Ioc a u, ENNReal.ofReal (A u - A s) := by
  set F : ℝ → ℝ → ℝ≥0∞ := fun U s => {p : ℝ × ℝ | p.2 < p.1}.indicator 1 (U, s) with hF
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_one.indicator (measurableSet_lt measurable_snd measurable_fst))
  have h1 : ∀ U ∈ Ioc a u, ENNReal.ofReal (U - a) = ∫⁻ s in Ioc a u, F U s := by
    intro U hU
    have : (fun s => F U s) = (Iio U).indicator 1 := by
      ext s; simp [hF, indicator]
    rw [this, lintegral_indicator measurableSet_Iio, Pi.one_def, setLIntegral_const, one_mul,
      Measure.restrict_apply measurableSet_Iio]
    have : Iio U ∩ Ioc a u = Ioo a U := by
      ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.le.trans hU.2⟩⟩
    rw [this, Real.volume_Ioo]
  have h2 : ∀ s ∈ Ioc a u, ∫⁻ U in Ioc a u, F U s ∂A.measure = ENNReal.ofReal (A u - A s) := by
    intro s hs
    have : (fun U => F U s) = (Ioi s).indicator 1 := by
      ext U; simp [hF, indicator]
    rw [this, lintegral_indicator measurableSet_Ioi, Pi.one_def, setLIntegral_const, one_mul,
      Measure.restrict_apply measurableSet_Ioi]
    have : Ioi s ∩ Ioc a u = Ioc s u := by
      ext U; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.1.trans h.1, h.2⟩⟩
    rw [this, A.measure_Ioc]
  rw [setLIntegral_congr_fun measurableSet_Ioc h1,
    lintegral_lintegral_swap hFm.aemeasurable, setLIntegral_congr_fun measurableSet_Ioc h2]

/-- The chain rule `(**)` on `(0, u]`: for `A` continuous on `[0, u]` and `g ∘ A ≥ U`,
`∫_{(0,u]} (g(A U) - U) dA(U) + ∫_0^u (A u - A U) dU = ∫_{A 0}^{A u} g`. -/
lemma chain_Ioc (A : StieltjesFunction ℝ) {g : ℝ → ℝ} (hg : Continuous g) {u : ℝ} (hu : 0 ≤ u)
    (hA : ContinuousOn A (Icc 0 u)) (hgA : ∀ U ∈ Ioc 0 u, U ≤ g (A U)) :
    ∫⁻ U in Ioc 0 u, ENNReal.ofReal (g (A U) - U) ∂A.measure +
        ∫⁻ U in Ioc 0 u, ENNReal.ofReal (A u - A U) =
      ∫⁻ t in Ioc (A 0) (A u), ENNReal.ofReal (g t) := by
  set X := ∫⁻ U in Ioc 0 u, ENNReal.ofReal U ∂A.measure with hX
  have hXfin : X ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal u * A.measure (Ioc 0 u)) ?_ ?_
    · rw [A.measure_Ioc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · rw [hX, ← setLIntegral_const]
      exact setLIntegral_mono measurable_const fun U hU => ENNReal.ofReal_le_ofReal hU.2
  have hX' : X = ∫⁻ U in Ioc 0 u, ENNReal.ofReal (A u - A U) := by
    rw [hX, ← lintegral_sub_dA A 0 u]; simp_rw [sub_zero]
  have hsum : ∫⁻ U in Ioc 0 u, ENNReal.ofReal (g (A U) - U) ∂A.measure + X =
      ∫⁻ U in Ioc 0 u, ENNReal.ofReal (g (A U)) ∂A.measure := by
    rw [hX, ← lintegral_add_right _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioc fun U hU => ?_
    rw [← ENNReal.ofReal_add (sub_nonneg.2 (hgA U hU)) hU.1.le, sub_add_cancel]
  have hmap : ∫⁻ U in Ioc 0 u, ENNReal.ofReal (g (A U)) ∂A.measure =
      ∫⁻ t in Ioc (A 0) (A u), ENNReal.ofReal (g t) := by
    rw [← map_measure_Ioc A hu hA,
      lintegral_map (by fun_prop) A.mono.measurable]
  rw [← ENNReal.add_left_inj hXfin, add_right_comm, hsum, hmap, ← hX']

/-- A set integral of a nonnegative continuous function on `(a, b]` as an interval integral. -/
lemma lintegral_Ioc_eq_ofReal {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b)
    (hg0 : ∀ t ∈ Ioc a b, 0 ≤ g t) :
    ∫⁻ t in Ioc a b, ENNReal.ofReal (g t) = ENNReal.ofReal (∫ t in a..b, g t) := by
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_restrict_of_forall_mem measurableSet_Ioc hg0)]

lemma iUnion_Ioc_seq {c : ℝ} {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Ioo 0 c)
    (hlim : Tendsto u atTop (𝓝 c)) : ⋃ n, Ioc 0 (u n) = Ioo 0 c := by
  ext U
  simp only [mem_iUnion, mem_Ioc, mem_Ioo]
  constructor
  · rintro ⟨n, h0, h1⟩; exact ⟨h0, h1.trans_lt (hu n).2⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds h1)).exists
    exact ⟨n, h0, (le_of_lt hn)⟩

/-- **One end of the decomposition.** Let `A` be continuous on `[0, c)` with `A ≤ p` there,
`g ≥ U` on `[A U, p]` and `∫_{A U}^p (g - U) → 0` as `U → c`. Then for `A 0 ≤ x ≤ p`,
`∫_0^c (x - A U)⁺ dU + ∫_{U ∈ (0,c), A U ≤ x} (g (A U) - U) dA(U) = ∫_{A 0}^x g`. -/
lemma left_cdf (A : StieltjesFunction ℝ) {g : ℝ → ℝ} (hg : Continuous g) {c p x : ℝ}
    (hc : 0 < c) (hAc : ContinuousOn A (Ico 0 c)) (hAp : ∀ U ∈ Ico 0 c, A U ≤ p)
    (hlev : ∀ U ∈ Ico 0 c, ∀ t ∈ Icc (A U) p, U ≤ g t)
    (hd : Tendsto (fun U => ∫ t in A U..p, (g t - U)) (𝓝[<] c) (𝓝 0))
    (hx0 : A 0 ≤ x) (hxp : x ≤ p) :
    (∫⁻ U in Ioo 0 c, ENNReal.ofReal (x - A U)) +
        ∫⁻ U in Ioo 0 c ∩ {U | A U ≤ x}, ENNReal.ofReal (g (A U) - U) ∂A.measure =
      ∫⁻ t in Ioc (A 0) x, ENNReal.ofReal (g t) := by
  have hgA : ∀ U ∈ Ico 0 c, U ≤ g (A U) := fun U hU => hlev U hU (A U) ⟨le_rfl, hAp U hU⟩
  by_cases hcase : ∃ U1 ∈ Ico 0 c, x < A U1
  · obtain ⟨U1, hU1, hxU1⟩ := hcase
    have hsub : Icc 0 U1 ⊆ Ico 0 c := fun U hU => ⟨hU.1, hU.2.trans_lt hU1.2⟩
    set S := {U ∈ Icc 0 U1 | A U ≤ x} with hS
    have hSc : IsClosed S := (hAc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
    have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hU1.1⟩, hx0⟩
    have hSb : BddAbove S := ⟨U1, fun U hU => hU.1.2⟩
    set v := sSup S with hv
    have hvS : v ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
    have hv0 : 0 ≤ v := le_csSup hSb h0S
    have hvc : v < c := hvS.1.2.trans_lt hU1.2
    have hAv : A v = x := by
      obtain ⟨w, hw, hwy⟩ := intermediate_value_Icc hvS.1.2
        (hAc.mono ((Icc_subset_Icc hvS.1.1 le_rfl).trans hsub)) ⟨hvS.2, hxU1.le⟩
      have hwS : w ∈ S := ⟨⟨hvS.1.1.trans hw.1, hw.2⟩, hwy.le⟩
      have : w = v := le_antisymm (le_csSup hSb hwS) hw.1
      rw [← this, hwy]
    have hgt : ∀ U, v < U → x < A U := by
      intro U hvU
      by_contra h
      push Not at h
      rcases le_or_gt U U1 with hUU1 | hUU1
      · exact absurd (le_csSup hSb ⟨⟨hv0.trans hvU.le, hUU1⟩, h⟩) (not_le.2 hvU)
      · exact absurd ((A.mono hUU1.le).trans h) (not_le.2 hxU1)
    have hset : Ioo 0 c ∩ {U | A U ≤ x} = Ioc 0 v := by
      ext U
      simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_Ioc]
      constructor
      · rintro ⟨⟨h0, -⟩, h⟩
        exact ⟨h0, not_lt.1 fun hvU => absurd h (not_le.2 (hgt U hvU))⟩
      · rintro ⟨h0, h⟩
        exact ⟨⟨h0, h.trans_lt hvc⟩, (A.mono h).trans hAv.le⟩
    have hK : ∫⁻ U in Ioo 0 c, ENNReal.ofReal (x - A U) =
        ∫⁻ U in Ioc 0 v, ENNReal.ofReal (A v - A U) := by
      rw [← Ioc_union_Ioo_eq_Ioo hv0 hvc, lintegral_union measurableSet_Ioo
        (disjoint_left.2 fun U (h1 : U ∈ Ioc 0 v) (h2 : U ∈ Ioo v c) => not_lt.2 h1.2 h2.1), hAv]
      have : ∫⁻ U in Ioo v c, ENNReal.ofReal (x - A U) = 0 := by
        rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0)
          (fun U hU => ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (hgt U hU.1).le)), lintegral_zero]
      rw [this, add_zero]
    rw [hset]
    rw [hK, add_comm, chain_Ioc A hg hv0 (hAc.mono (Icc_subset_Ico_right hvc))
      (fun U hU => hgA U ⟨hU.1.le, hU.2.trans_lt hvc⟩), hAv]
  push Not at hcase
  -- all of `[0, c)` is below `x`: pass to the limit `U → c`
  have hset : Ioo 0 c ∩ {U | A U ≤ x} = Ioo 0 c :=
    inter_eq_left.2 fun U hU => hcase U ⟨hU.1.le, hU.2⟩
  rw [hset]
  have hc0 : (0 : ℝ) ∈ Ico 0 c := ⟨le_rfl, hc⟩
  set L := sSup (A '' Iio c) with hLdef
  have hL : Tendsto A (𝓝[<] c) (𝓝 L) := A.mono.tendsto_nhdsLT c
  have hbdd : BddAbove (A '' Iio c) := by
    refine ⟨x, ?_⟩
    rintro _ ⟨U, hU, rfl⟩
    rcases lt_or_ge U 0 with h | h
    · exact (A.mono h.le).trans hx0
    · exact hcase U ⟨h, hU⟩
  have hAL : ∀ U < c, A U ≤ L := fun U hU => le_csSup hbdd ⟨U, hU, rfl⟩
  have hne : (A '' Iio c).Nonempty := ⟨A 0, mem_image_of_mem _ (show (0 : ℝ) ∈ Iio c from hc)⟩
  have hLx : L ≤ x := by
    apply csSup_le hne
    rintro _ ⟨U, hU, rfl⟩
    rcases lt_or_ge U 0 with h | h
    · exact (A.mono h.le).trans hx0
    · exact hcase U ⟨h, hU⟩
  have hL0 : A 0 ≤ L := hAL 0 hc
  have hLp : L ≤ p := hLx.trans hxp
  have hg0 : ∀ t ∈ Icc (A 0) p, 0 ≤ g t := fun t ht => hlev 0 hc0 t ht
  have hgc : ∀ t ∈ Icc L p, c ≤ g t := by
    intro t ht
    by_contra h
    push Not at h
    set U := max 0 ((g t + c) / 2)
    have hU : U ∈ Ico 0 c := ⟨le_max_left _ _, max_lt hc (by linarith)⟩
    have := hlev U hU t ⟨(hAL U hU.2).trans ht.1, ht.2⟩
    have : (g t + c) / 2 ≤ U := le_max_right _ _
    linarith
  have hint : ∀ a b : ℝ, ∀ k : ℝ, IntervalIntegrable (fun t => g t - k) volume a b :=
    fun a b k => (hg.sub continuous_const).intervalIntegrable a b
  -- the frozen part: `g = c` on `[L, p]` in the sense of integrals
  have hLp0 : ∫ t in L..p, (g t - c) ≤ 0 := by
    have hlim : Tendsto (fun U => ∫ t in L..p, (g t - U)) (𝓝[<] c)
        (𝓝 (∫ t in L..p, (g t - c))) := by
      have : (fun U => ∫ t in L..p, (g t - U)) =
          fun U => (∫ t in L..p, g t) - (p - L) * U := by
        ext U
        rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
      rw [this, intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
      exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        tendsto_id)).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim hd ?_
    filter_upwards [Ioo_mem_nhdsLT hc] with U hU
    have hU' : U ∈ Ico 0 c := ⟨hU.1.le, hU.2⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint (A U) L U) (hint L p U)]
    have : 0 ≤ ∫ t in A U..L, (g t - U) :=
      intervalIntegral.integral_nonneg (hAL U hU.2) fun t ht =>
        sub_nonneg.2 (hlev U hU' t ⟨ht.1, ht.2.trans hLp⟩)
    linarith
  have hkey : ∫ t in L..x, g t = c * (x - L) := by
    have h1 : 0 ≤ ∫ t in L..x, (g t - c) := intervalIntegral.integral_nonneg hLx
      fun t ht => sub_nonneg.2 (hgc t ⟨ht.1, ht.2.trans hxp⟩)
    have h2 : 0 ≤ ∫ t in x..p, (g t - c) := intervalIntegral.integral_nonneg hxp
      fun t ht => sub_nonneg.2 (hgc t ⟨hLx.trans ht.1, ht.2⟩)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint L x c) (hint x p c)] at hLp0
    have h3 : ∫ t in L..x, (g t - c) = 0 := by linarith
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h3
    linarith
  -- the limit along a sequence `u n ↑ c`
  obtain ⟨u, hu_mono, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' hc
  have hU := iUnion_Ioc_seq hu_mem hu_lim
  have hmonoS : Monotone fun n => Ioc (0 : ℝ) (u n) :=
    fun m n h => Ioc_subset_Ioc_right (hu_mono.monotone h)
  have hT1 : Tendsto (fun n => ∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (g (A U) - U) ∂A.measure)
      atTop (𝓝 (∫⁻ U in Ioo 0 c, ENNReal.ofReal (g (A U) - U) ∂A.measure)) := by
    have := tendsto_measure_iUnion_atTop
      (μ := A.measure.withDensity fun U => ENNReal.ofReal (g (A U) - U)) hmonoS
    rw [hU, withDensity_apply _ measurableSet_Ioo] at this
    simpa [Function.comp_def, withDensity_apply _ measurableSet_Ioc] using this
  have hT2 : Tendsto (fun n => ∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (x - A U))
      atTop (𝓝 (∫⁻ U in Ioo 0 c, ENNReal.ofReal (x - A U))) := by
    have := tendsto_measure_iUnion_atTop
      (μ := volume.withDensity fun U => ENNReal.ofReal (x - A U)) hmonoS
    rw [hU, withDensity_apply _ measurableSet_Ioo] at this
    simpa [Function.comp_def, withDensity_apply _ measurableSet_Ioc] using this
  have hseq : ∀ n, (∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (x - A U)) +
      ∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (g (A U) - U) ∂A.measure =
      ENNReal.ofReal ((∫ t in A 0..A (u n), g t) + u n * (x - A (u n))) := by
    intro n
    have hun := hu_mem n
    have hxu : 0 ≤ x - A (u n) := sub_nonneg.2 (hcase _ ⟨hun.1.le, hun.2⟩)
    have hsplit : ∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (x - A U) =
        (∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (A (u n) - A U)) +
          ENNReal.ofReal (u n * (x - A (u n))) := by
      have : ∀ U ∈ Ioc 0 (u n), ENNReal.ofReal (x - A U) =
          ENNReal.ofReal (A (u n) - A U) + ENNReal.ofReal (x - A (u n)) := fun U hU => by
        rw [← ENNReal.ofReal_add (sub_nonneg.2 (A.mono hU.2)) hxu]; ring_nf
      rw [setLIntegral_congr_fun measurableSet_Ioc this, lintegral_add_right _ measurable_const,
        setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hxu, mul_comm]
    have hint0 : 0 ≤ ∫ t in A 0..A (u n), g t :=
      intervalIntegral.integral_nonneg (A.mono hun.1.le)
        fun t ht => hg0 t ⟨ht.1, ht.2.trans (hAp _ ⟨hun.1.le, hun.2⟩)⟩
    rw [hsplit, add_right_comm, add_comm (∫⁻ U in Ioc 0 (u n), ENNReal.ofReal (A (u n) - A U)),
      chain_Ioc A hg hun.1.le (hAc.mono (Icc_subset_Ico_right hun.2))
        (fun U hU => hgA U ⟨hU.1.le, hU.2.trans_lt hun.2⟩),
      lintegral_Ioc_eq_ofReal hg (A.mono hun.1.le)
        (fun t ht => hg0 t ⟨ht.1.le, ht.2.trans (hAp _ ⟨hun.1.le, hun.2⟩)⟩),
      ← ENNReal.ofReal_add hint0 (mul_nonneg hun.1.le hxu)]
  have hAu : Tendsto (fun n => A (u n)) atTop (𝓝 L) :=
    hL.comp (tendsto_nhdsWithin_iff.2 ⟨hu_lim, Eventually.of_forall fun n => (hu_mem n).2⟩)
  have hprim : Continuous fun y => ∫ t in A 0..y, g t :=
    intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) (A 0)
  have hR : Tendsto (fun n => ENNReal.ofReal ((∫ t in A 0..A (u n), g t) + u n * (x - A (u n))))
      atTop (𝓝 (ENNReal.ofReal ((∫ t in A 0..L, g t) + c * (x - L)))) :=
    ENNReal.tendsto_ofReal (((hprim.tendsto L).comp hAu).add
      (hu_lim.mul (tendsto_const_nhds.sub hAu)))
  rw [tendsto_nhds_unique ((hT2.add hT1).congr hseq) hR,
    lintegral_Ioc_eq_ofReal hg hx0 (fun t ht => hg0 t ⟨ht.1.le, ht.2.trans hxp⟩),
    ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable (A 0) L)
      (hg.intervalIntegrable L x), hkey]

/-! ### The pieces `π_U` -/

/-- The atom at the left end, `(r² - ℓ²)⁺ / (2ℓ)` with `ℓ = μ - a`, `r = b - μ`. -/
def wL (μ a b : ℝ) : ℝ := max ((b - μ) ^ 2 - (μ - a) ^ 2) 0 / (2 * (μ - a))

/-- The atom at the right end, `(ℓ² - r²)⁺ / (2r)` with `ℓ = μ - a`, `r = b - μ`. -/
def wR (μ a b : ℝ) : ℝ := max ((μ - a) ^ 2 - (b - μ) ^ 2) 0 / (2 * (b - μ))

/-- The measure `π = 1_{[a,b]} dx + wL δ_a + wR δ_b` of Theorem 35, for `a = A(U)`, `b = B(U)`. -/
def piU (μ a b : ℝ) : Measure ℝ :=
  volume.restrict (Icc a b) + ENNReal.ofReal (wL μ a b) • Measure.dirac a +
    ENNReal.ofReal (wR μ a b) • Measure.dirac b

lemma measurable_piU (μ : ℝ) {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun U => piU μ (a U) (b U) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [piU, add_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Measure.restrict_apply hs]
  have hT : MeasurableSet {q : ℝ × ℝ | a q.1 ≤ q.2 ∧ q.2 ≤ b q.1 ∧ q.2 ∈ s} :=
    (measurableSet_le (ha.comp measurable_fst) measurable_snd).inter
      ((measurableSet_le measurable_snd (hb.comp measurable_fst)).inter (measurable_snd hs))
  have h1 : Measurable fun U => volume (s ∩ Icc (a U) (b U)) := by
    have : ∀ U, s ∩ Icc (a U) (b U) =
        Prod.mk U ⁻¹' {q : ℝ × ℝ | a q.1 ≤ q.2 ∧ q.2 ≤ b q.1 ∧ q.2 ∈ s} := by
      intro U; ext t; simp only [mem_inter_iff, mem_Icc, mem_preimage, mem_ofPred_eq]; tauto
    simp_rw [this]
    exact measurable_measure_prodMk_left hT
  have hwL : Measurable fun U => wL μ (a U) (b U) := by unfold wL; fun_prop
  have hwR : Measurable fun U => wR μ (a U) (b U) := by unfold wR; fun_prop
  refine (h1.add ((ENNReal.measurable_ofReal.comp hwL).mul
    ((measurable_one.indicator hs).comp ha))).add ((ENNReal.measurable_ofReal.comp hwR).mul
    ((measurable_one.indicator hs).comp hb))

lemma piU_Iic {μ a b x : ℝ} (hxb : x < b) :
    piU μ a b (Iic x) = ENNReal.ofReal (x - a) + {a' : ℝ | a' ≤ x}.indicator
      (fun _ => ENNReal.ofReal (wL μ a b)) a := by
  simp only [piU, add_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have : Iic x ∩ Icc a b = Icc a x := by
    ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hxb.le⟩⟩
  rw [this, Real.volume_Icc, indicator_of_notMem (show b ∉ Iic x from not_le.2 hxb), mul_zero,
    add_zero]
  by_cases hax : a ≤ x
  · simp [hax]
  · simp [hax]

lemma piU_Ici {μ a b y : ℝ} (hay : a < y) :
    piU μ a b (Ici y) = ENNReal.ofReal (b - y) + {b' : ℝ | y ≤ b'}.indicator
      (fun _ => ENNReal.ofReal (wR μ a b)) b := by
  simp only [piU, add_apply, smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
  have : Ici y ∩ Icc a b = Icc y b := by
    ext t; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hay.le.trans h.1, h.2⟩⟩
  rw [this, Real.volume_Icc, indicator_of_notMem (show a ∉ Ici y from not_le.2 hay), mul_zero,
    add_zero]
  by_cases hby : y ≤ b
  · simp [hby]
  · simp [hby]

/-! ### The facts of Theorem 34 used here -/

/-- The facts of Theorem 34 (`c:thm:peel`) used in Theorem 35, stated as hypotheses (Theorem 34
is proved separately). `f` is the density (continuous; a continuous function on `[0,1]` can be
extended continuously to `ℝ` without changing the distribution), `μ` its mean, `A`, `B` the ends
of the peeled intervals, `SA`, `SB` Stieltjes functions extending `A` and `-B` from `[0, f μ)`,
so that `dA = SA.measure` and `d(-B) = SB.measure` on `(0, f μ)`. -/
structure Peel34 (f : ℝ → ℝ) (μ : ℝ) (A B : ℝ → ℝ) (SA SB : StieltjesFunction ℝ) : Prop where
  cont : Continuous f
  pos : 0 < f μ
  /-- Theorem 34(b): `A(0) = 0`, `B(0) = 1`. -/
  A0 : A 0 = 0
  B0 : B 0 = 1
  /-- Theorem 34(b): `A(U) < μ < B(U)`. -/
  A_lt : ∀ U ∈ Ico 0 (f μ), A U < μ
  lt_B : ∀ U ∈ Ico 0 (f μ), μ < B U
  /-- Theorem 34(b): `A` and `B` are continuous (their monotonicity is carried by `SA`, `SB`). -/
  A_cont : ContinuousOn A (Ico 0 (f μ))
  B_cont : ContinuousOn B (Ico 0 (f μ))
  SA_eq : EqOn SA A (Ico 0 (f μ))
  SB_eq : EqOn SB (fun U => -B U) (Ico 0 (f μ))
  /-- Theorem 34(b), `a(U) ≤ A(U)` and `B(U) ≤ b(U)`: `f ≥ U` on `[A(U), B(U)]`. -/
  lev : ∀ U ∈ Ico 0 (f μ), ∀ t ∈ Icc (A U) (B U), U ≤ f t
  /-- Theorem 34(c), left end: `(f(A(U)) - U) dA(U) = (r² - ℓ²)⁺/(2ℓ) dU`. -/
  dA : (SA.measure.restrict (Ioo 0 (f μ))).withDensity (fun U => ENNReal.ofReal (f (A U) - U)) =
    (volume.restrict (Ioo 0 (f μ))).withDensity (fun U => ENNReal.ofReal (wL μ (A U) (B U)))
  /-- Theorem 34(c), right end: `(f(B(U)) - U) d(-B)(U) = (ℓ² - r²)⁺/(2r) dU`. -/
  dB : (SB.measure.restrict (Ioo 0 (f μ))).withDensity (fun U => ENNReal.ofReal (f (B U) - U)) =
    (volume.restrict (Ioo 0 (f μ))).withDensity (fun U => ENNReal.ofReal (wR μ (A U) (B U)))
  /-- Theorem 34(d): `∫_{A(U)}^{B(U)} (f - U) → 0` as `U → f(μ)`. -/
  lim : Tendsto (fun U => ∫ t in A U..B U, (f t - U)) (𝓝[<] (f μ)) (𝓝 0)

/-! ### Theorem 35 -/

/-- **Theorem 35, decomposition (`c:eq:decomp`).** Under the conclusions of Theorem 34, the mixture
`∫_0^{f(μ)} π_U dU` of the measures `π_U` equals the distribution `f(x) dx` on `[0, 1]`. -/
theorem decomp {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} {SA SB : StieltjesFunction ℝ}
    (h : Peel34 f μ A B SA SB) :
    (volume.restrict (Ioo 0 (f μ))).bind (fun U => piU μ (A U) (B U)) =
      (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hf := h.cont
  set c := f μ with hcdef
  have hc : 0 < c := h.pos
  have hc0 : (0 : ℝ) ∈ Ico 0 c := ⟨le_rfl, hc⟩
  have hI : ∀ U ∈ Ioo 0 c, U ∈ Ico 0 c := fun U hU => ⟨hU.1.le, hU.2⟩
  have hSAm : Measurable SA := SA.mono.measurable
  have hSBm : Measurable SB := SB.mono.measurable
  have hπae : AEMeasurable (fun U => piU μ (A U) (B U)) (volume.restrict (Ioo 0 c)) := by
    refine (measurable_piU μ hSAm hSBm.neg).aemeasurable.congr
      ((ae_restrict_mem measurableSet_Ioo).mono fun U hU => ?_)
    simp only [Pi.neg_apply, h.SA_eq (hI U hU), h.SB_eq (hI U hU), neg_neg]
  have hμ0 : 0 < μ := by have := h.A_lt 0 hc0; rwa [h.A0] at this
  have hμ1 : μ < 1 := by have := h.lt_B 0 hc0; rwa [h.B0] at this
  have hSA0 : SA 0 = 0 := (h.SA_eq hc0).trans h.A0
  have hSB0 : SB 0 = -1 := by rw [h.SB_eq hc0]; simp [h.B0]
  have hfnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t := fun t ht =>
    h.lev 0 hc0 t (by rw [h.A0, h.B0]; exact ht)
  have hAc : ContinuousOn SA (Ico 0 c) := h.A_cont.congr h.SA_eq
  have hBc : ContinuousOn SB (Ico 0 c) := h.B_cont.neg.congr h.SB_eq
  have hint : ∀ a b U : ℝ, IntervalIntegrable (fun t => f t - U) volume a b :=
    fun a b U => (hf.sub continuous_const).intervalIntegrable a b
  -- Theorem 34(d) at each end
  have hsplit : ∀ U ∈ Ioo 0 c, 0 ≤ ∫ t in A U..μ, (f t - U) ∧ 0 ≤ ∫ t in μ..B U, (f t - U) ∧
      (∫ t in A U..μ, (f t - U)) + ∫ t in μ..B U, (f t - U) = ∫ t in A U..B U, (f t - U) := by
    intro U hU
    have hU' := hI U hU
    refine ⟨intervalIntegral.integral_nonneg (h.A_lt U hU').le fun t ht =>
        sub_nonneg.2 (h.lev U hU' t ⟨ht.1, ht.2.trans (h.lt_B U hU').le⟩),
      intervalIntegral.integral_nonneg (h.lt_B U hU').le fun t ht =>
        sub_nonneg.2 (h.lev U hU' t ⟨(h.A_lt U hU').le.trans ht.1, ht.2⟩),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _ _) (hint _ _ _)⟩
  have hdL : Tendsto (fun U => ∫ t in SA U..μ, (f t - U)) (𝓝[<] c) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.lim ?_ ?_ <;>
      filter_upwards [Ioo_mem_nhdsLT hc] with U hU <;> rw [h.SA_eq (hI U hU)] <;>
      obtain ⟨h1, h2, h3⟩ := hsplit U hU <;> linarith
  have hdR : Tendsto (fun U => ∫ t in SB U..-μ, (f (-t) - U)) (𝓝[<] c) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.lim ?_ ?_ <;>
      filter_upwards [Ioo_mem_nhdsLT hc] with U hU <;>
      rw [intervalIntegral.integral_comp_neg (fun t => f t - U), h.SB_eq (hI U hU), neg_neg,
        neg_neg] <;>
      obtain ⟨h1, h2, h3⟩ := hsplit U hU <;> linarith
  have hSBU : ∀ U ∈ Ico 0 c, SB U = -B U := fun U hU => h.SB_eq hU
  -- the left half: `Iic x` for `x ≤ μ`
  have hνL : ∀ x ≤ μ, (volume.restrict (Ioo 0 c)).bind (fun U => piU μ (A U) (B U)) (Iic x) =
      (∫⁻ U in Ioo 0 c, ENNReal.ofReal (x - SA U)) +
        ∫⁻ U in Ioo 0 c ∩ {U | SA U ≤ x}, ENNReal.ofReal (f (SA U) - U) ∂SA.measure := by
    intro x hx
    rw [Measure.bind_apply measurableSet_Iic hπae]
    have hS : MeasurableSet {U | SA U ≤ x} := measurableSet_le hSAm measurable_const
    have : ∀ U ∈ Ioo 0 c, piU μ (A U) (B U) (Iic x) = ENNReal.ofReal (x - SA U) +
        {U | SA U ≤ x}.indicator (fun U => ENNReal.ofReal (wL μ (A U) (B U))) U := by
      intro U hU
      rw [piU_Iic (hx.trans_lt (h.lt_B U (hI U hU))), h.SA_eq (hI U hU)]
      simp only [indicator, mem_ofPred_eq, h.SA_eq (hI U hU)]
    rw [setLIntegral_congr_fun measurableSet_Ioo this,
      lintegral_add_left (show Measurable fun U => ENNReal.ofReal (x - SA U) by fun_prop),
      lintegral_indicator hS, ← withDensity_apply _ hS, ← h.dA, withDensity_apply _ hS,
      Measure.restrict_restrict hS, inter_comm]
    congr 1
    exact setLIntegral_congr_fun (measurableSet_Ioo.inter hS)
      fun U hU => by rw [h.SA_eq (hI U hU.1)]
  have hνL' : ∀ x ≤ μ, (volume.restrict (Ioo 0 c)).bind (fun U => piU μ (A U) (B U)) (Iic x) =
      (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) (Iic x) := by
    intro x hx
    rw [hνL x hx, withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic]
    rcases lt_or_ge x 0 with hx0 | hx0
    · have h1 : Iic x ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1, h.2.1]
      have h2 : Ioo 0 c ∩ {U | SA U ≤ x} = ∅ := by
        ext U; simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h; linarith [SA.mono h.1.1.le, h.2]
      rw [h1, h2, Measure.restrict_empty, Measure.restrict_empty, lintegral_zero_measure,
        lintegral_zero_measure, add_zero]
      refine (setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) fun U hU => ?_).trans
        lintegral_zero
      exact ENNReal.ofReal_eq_zero.2 (by linarith [SA.mono hU.1.le])
    have h1 : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 x := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith⟩
    rw [h1, setLIntegral_congr Ioc_ae_eq_Icc.symm]
    have := left_cdf SA hf hc hAc (p := μ) (fun U hU => by rw [h.SA_eq hU]; exact (h.A_lt U hU).le)
      (fun U hU t ht => h.lev U hU t ⟨by rw [← h.SA_eq hU]; exact ht.1,
        ht.2.trans (h.lt_B U hU).le⟩) hdL (by rw [hSA0]; exact hx0) hx
    rwa [hSA0] at this
  -- the right half: `Ici y` for `μ ≤ y`
  have hνR : ∀ y, μ ≤ y → (volume.restrict (Ioo 0 c)).bind (fun U => piU μ (A U) (B U)) (Ici y) =
      (∫⁻ U in Ioo 0 c, ENNReal.ofReal (-y - SB U)) +
        ∫⁻ U in Ioo 0 c ∩ {U | SB U ≤ -y}, ENNReal.ofReal (f (-SB U) - U) ∂SB.measure := by
    intro y hy
    rw [Measure.bind_apply measurableSet_Ici hπae]
    have hS : MeasurableSet {U | SB U ≤ -y} := measurableSet_le hSBm measurable_const
    have : ∀ U ∈ Ioo 0 c, piU μ (A U) (B U) (Ici y) = ENNReal.ofReal (-y - SB U) +
        {U | SB U ≤ -y}.indicator (fun U => ENNReal.ofReal (wR μ (A U) (B U))) U := by
      intro U hU
      rw [piU_Ici ((h.A_lt U (hI U hU)).trans_le hy), hSBU U (hI U hU), sub_neg_eq_add,
        neg_add_eq_sub]
      simp only [indicator, mem_ofPred_eq, hSBU U (hI U hU), neg_le_neg_iff]
    rw [setLIntegral_congr_fun measurableSet_Ioo this,
      lintegral_add_left (show Measurable fun U => ENNReal.ofReal (-y - SB U) by fun_prop),
      lintegral_indicator hS, ← withDensity_apply _ hS, ← h.dB, withDensity_apply _ hS,
      Measure.restrict_restrict hS, inter_comm]
    congr 1
    exact setLIntegral_congr_fun (measurableSet_Ioo.inter hS)
      fun U hU => by rw [hSBU U (hI U hU.1), neg_neg]
  have hνR' : ∀ y, μ ≤ y →
      (volume.restrict (Ioo 0 c)).bind (fun U => piU μ (A U) (B U)) (Ici y) =
      (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) (Ici y) := by
    intro y hy
    rw [hνR y hy, withDensity_apply _ measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    rcases lt_or_ge 1 y with hy1 | hy1
    · have h1 : Ici y ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext t; simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1, h.2.2]
      have h2 : Ioo 0 c ∩ {U | SB U ≤ -y} = ∅ := by
        ext U; simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h; linarith [SB.mono h.1.1.le, h.2]
      rw [h1, h2, Measure.restrict_empty, Measure.restrict_empty, lintegral_zero_measure,
        lintegral_zero_measure, add_zero]
      refine (setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) fun U hU => ?_).trans
        lintegral_zero
      exact ENNReal.ofReal_eq_zero.2 (by linarith [SB.mono hU.1.le])
    have h1 : Ici y ∩ Icc (0 : ℝ) 1 = Icc y 1 := by
      ext t; simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
    rw [h1, setLIntegral_congr Ioc_ae_eq_Icc.symm, lintegral_Ioc_eq_ofReal hf hy1
      (fun t ht => hfnn t ⟨by linarith [ht.1], ht.2⟩)]
    have := left_cdf SB (g := fun t => f (-t)) (hf.comp continuous_neg) hc hBc (p := -μ) (x := -y)
      (fun U hU => by rw [hSBU U hU]; exact neg_le_neg (h.lt_B U hU).le)
      (fun U hU t ht => by
        have h1 := ht.1; rw [hSBU U hU] at h1
        exact h.lev U hU (-t) ⟨(h.A_lt U hU).le.trans (by linarith [ht.2]), by linarith⟩)
      hdR (by rw [hSB0]; linarith) (by linarith)
    have hconv := lintegral_Ioc_eq_ofReal (g := fun t => f (-t)) (a := -1) (b := -y)
      (hf.comp continuous_neg) (by linarith)
      (fun t ht => hfnn (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    rw [this, hSB0, hconv, intervalIntegral.integral_comp_neg (fun t => f t), neg_neg, neg_neg]
  set ν := (volume.restrict (Ioo 0 c)).bind (fun U => piU μ (A U) (B U)) with hν
  set ρ := (volume.restrict (Icc 0 1)).withDensity (fun x => ENNReal.ofReal (f x)) with hρ
  have hρfin : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hf.integrableOn_Icc.2
  have hIoi : ∀ y, μ ≤ y → ν (Ioi y) = ρ (Ioi y) := by
    intro y hy
    have hU : ⋃ n : ℕ, Ici (y + 1 / ((n : ℝ) + 1)) = Ioi y := by
      ext t; simp only [mem_iUnion, mem_Ici, mem_Ioi]
      constructor
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
        linarith
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ht)
        exact ⟨n, by linarith⟩
    have hmono : Monotone fun n : ℕ => Ici (y + 1 / ((n : ℝ) + 1)) := fun m n hmn =>
      Ici_subset_Ici.2 (by have := Nat.one_div_le_one_div (α := ℝ) hmn; linarith)
    have h1 := tendsto_measure_iUnion_atTop (μ := ν) hmono
    have h2 := tendsto_measure_iUnion_atTop (μ := ρ) hmono
    rw [hU] at h1 h2
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    simp only [Function.comp_apply]
    exact (hνR' _ (by linarith)).symm
  have huniv : ν univ = ρ univ := by
    rw [← Iic_union_Ioi (a := μ), measure_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
      measure_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, hνL' μ le_rfl, hIoi μ le_rfl]
  have : IsFiniteMeasure ν := ⟨by rw [huniv]; exact measure_lt_top ρ univ⟩
  refine Measure.ext_of_Iic ν ρ fun x => ?_
  rcases le_or_gt x μ with hx | hx
  · exact hνL' x hx
  · rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top ν _),
      measure_compl measurableSet_Ioi (measure_ne_top ρ _), huniv, hIoi x hx.le]

/-! ### `π_U` as a scaled affine image of `P_β` -/

/-- The image of Lebesgue measure on `[0, β]` under `y ↦ a₀ + k y`, `k ≠ 0`. -/
lemma map_restrict_affine (a₀ k β : ℝ) (hk : k ≠ 0) (hβ : 0 ≤ β) :
    (volume.restrict (Icc 0 β)).map (fun y => a₀ + k * y) =
      ENNReal.ofReal |k⁻¹| • volume.restrict (uIcc a₀ (a₀ + k * β)) := by
  have hg : Measurable fun y : ℝ => a₀ + k * y := by fun_prop
  ext s hs
  rw [Measure.map_apply hg hs, Measure.restrict_apply (hg hs), smul_apply, smul_eq_mul,
    Measure.restrict_apply hs]
  have hpre : (fun y : ℝ => a₀ + k * y) ⁻¹' s ∩ Icc 0 β =
      (fun y => k * y) ⁻¹' ((fun y => a₀ + y) ⁻¹' (s ∩ uIcc a₀ (a₀ + k * β))) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    rcases hk.lt_or_gt with hk | hk
    · rw [uIcc_of_ge (by nlinarith)]
      simp only [mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩
        · by_contra h; push Not at h; nlinarith
        · by_contra h; push Not at h; nlinarith
    · rw [uIcc_of_le (by nlinarith)]
      simp only [mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩
        · by_contra h; push Not at h; nlinarith
        · by_contra h; push Not at h; nlinarith
  rw [hpre, Real.volume_preimage_mul_left hk, measure_preimage_add]

/-- The total mass `W = (ℓ + r)² / (2 min(ℓ, r))`. -/
def W (μ a b : ℝ) : ℝ := ((μ - a) + (b - μ)) ^ 2 / (2 * min (μ - a) (b - μ))

/-- The ratio `β = (ℓ + r) / min(ℓ, r)`. -/
def beta (μ a b : ℝ) : ℝ := ((μ - a) + (b - μ)) / min (μ - a) (b - μ)

lemma two_le_beta {μ a b : ℝ} (ha : a < μ) (hb : μ < b) : 2 ≤ beta μ a b := by
  unfold beta
  rw [le_div_iff₀ (lt_min (by linarith) (by linarith))]
  have := min_le_left (μ - a) (b - μ); have := min_le_right (μ - a) (b - μ); linarith

lemma unifI_eq {l r : ℝ} (hlr : l < r) :
    unifI l r = (ENNReal.ofReal (r - l))⁻¹ • volume.restrict (Icc l r) := by
  simp [unifI, hlr]

/-- Scaling: `W • (1 - 2/β) δ_e + W • (2/β) U[a,b] = π`, given the atom weight. -/
lemma piU_of_weights {μ a b e we : ℝ} (hab : a < b) (hβ : 2 ≤ beta μ a b)
    (hW2 : W μ a b * (2 / beta μ a b) = b - a)
    (hW1 : W μ a b * (1 - 2 / beta μ a b) = we)
    (hpi : piU μ a b = volume.restrict (Icc a b) + ENNReal.ofReal we • Measure.dirac e) :
    ENNReal.ofReal (W μ a b) • (ENNReal.ofReal (1 - 2 / beta μ a b) • Measure.dirac e +
      ENNReal.ofReal (2 / beta μ a b) • unifI a b) = piU μ a b := by
  have hβ0 : 0 < beta μ a b := by linarith
  have hW0 : 0 ≤ W μ a b := by
    have : 0 < 2 / beta μ a b := by positivity
    nlinarith
  have h1 : 0 ≤ 1 - 2 / beta μ a b := by
    rw [sub_nonneg, div_le_one hβ0]; exact hβ
  rw [hpi, unifI_eq hab, smul_add, smul_smul, smul_smul, smul_smul, ← ENNReal.ofReal_mul hW0,
    ← ENNReal.ofReal_mul hW0, hW1, hW2, ENNReal.mul_inv_cancel
      (by simpa using hab) ENNReal.ofReal_ne_top, one_smul, add_comm]

/-- **Theorem 35, the pieces, case `ℓ ≤ r`.** `π_U` is `W(U)` times the image of `P_{β(U)}`
under `y ↦ μ - ℓ + ℓ y`. -/
theorem piU_eq_left {μ a b : ℝ} (ha : a < μ) (hb : μ < b) (hle : μ - a ≤ b - μ) :
    piU μ a b = ENNReal.ofReal (W μ a b) •
      (pieceP (beta μ a b)).map (fun y => μ - (μ - a) + (μ - a) * y) := by
  have hℓ : 0 < μ - a := by linarith
  have hmin : min (μ - a) (b - μ) = μ - a := min_eq_left hle
  have hβ := two_le_beta ha hb
  have hβ' : beta μ a b = (b - a) / (μ - a) := by rw [beta, hmin]; ring_nf
  have hg : Measurable fun y : ℝ => μ - (μ - a) + (μ - a) * y := by fun_prop
  have hmap : (unifI 0 (beta μ a b)).map (fun y => μ - (μ - a) + (μ - a) * y) = unifI a b := by
    have e1 : μ - (μ - a) = a := by ring
    have e2 : a + (μ - a) * ((b - a) / (μ - a)) = b := by field_simp; ring
    have hq : 0 < (b - a) / (μ - a) := div_pos (by linarith) hℓ
    rw [unifI_eq (by linarith : (0 : ℝ) < beta μ a b), unifI_eq (by linarith : a < b),
      Measure.map_smul _ hg.aemeasurable, map_restrict_affine _ _ _ hℓ.ne' (by linarith), smul_smul,
      hβ', e1, e2,
      uIcc_of_le (by linarith), abs_of_pos (inv_pos.2 hℓ), sub_zero,
      ← ENNReal.ofReal_inv_of_pos hq, ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le),
      ← ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < b - a)]
    congr 2
    field_simp
  have hd0 : unifI 0 0 = Measure.dirac 0 := by simp [unifI]
  have e0 : μ - (μ - a) + (μ - a) * 0 = a := by ring
  rw [pieceP, Measure.map_add _ _ hg, Measure.map_smul _ hg.aemeasurable,
    Measure.map_smul _ hg.aemeasurable, hmap, hd0,
    Measure.map_dirac' hg, e0]
  refine (piU_of_weights (we := wL μ a b) (by linarith) hβ ?_ ?_ ?_).symm
  · rw [W, beta, hmin]; field_simp; ring
  · rw [wL, W, beta, hmin, max_eq_left (by nlinarith)]
    field_simp; ring
  · have : wR μ a b = 0 := by
      rw [wR, max_eq_right (by nlinarith), zero_div]
    rw [piU, this, ENNReal.ofReal_zero, zero_smul, add_zero]

/-- **Theorem 35, the pieces, case `ℓ > r`.** `π_U` is `W(U)` times the image of `P_{β(U)}`
under `y ↦ μ + r - r y`. -/
theorem piU_eq_right {μ a b : ℝ} (ha : a < μ) (hb : μ < b) (hlt : b - μ < μ - a) :
    piU μ a b = ENNReal.ofReal (W μ a b) •
      (pieceP (beta μ a b)).map (fun y => μ + (b - μ) - (b - μ) * y) := by
  have hr : 0 < b - μ := by linarith
  have hmin : min (μ - a) (b - μ) = b - μ := min_eq_right hlt.le
  have hβ := two_le_beta ha hb
  have hβ' : beta μ a b = (b - a) / (b - μ) := by rw [beta, hmin]; ring_nf
  have hfun : (fun y => μ + (b - μ) - (b - μ) * y) = fun y => b + (-(b - μ)) * y := by
    ext y; ring
  rw [hfun]
  have hg : Measurable fun y : ℝ => b + (-(b - μ)) * y := by fun_prop
  have hmap : (unifI 0 (beta μ a b)).map (fun y => b + (-(b - μ)) * y) = unifI a b := by
    have e2 : b + -(b - μ) * ((b - a) / (b - μ)) = a := by field_simp; ring
    have hq : 0 < (b - a) / (b - μ) := div_pos (by linarith) hr
    rw [unifI_eq (by linarith : (0 : ℝ) < beta μ a b), unifI_eq (by linarith : a < b),
      Measure.map_smul _ hg.aemeasurable, map_restrict_affine _ _ _ (by linarith)
        (by linarith), smul_smul, hβ', e2, uIcc_of_ge (by linarith), inv_neg, abs_neg,
      abs_of_pos (inv_pos.2 hr), sub_zero, ← ENNReal.ofReal_inv_of_pos hq,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hq.le),
      ← ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < b - a)]
    congr 2
    field_simp
  have hd0 : unifI 0 0 = Measure.dirac 0 := by simp [unifI]
  have e0 : b + -(b - μ) * 0 = b := by ring
  rw [pieceP, Measure.map_add _ _ hg, Measure.map_smul _ hg.aemeasurable,
    Measure.map_smul _ hg.aemeasurable, hmap, hd0, Measure.map_dirac' hg, e0]
  refine (piU_of_weights (we := wR μ a b) (by linarith) hβ ?_ ?_ ?_).symm
  · rw [W, beta, hmin]; field_simp; ring
  · rw [wR, W, beta, hmin, max_eq_left (by nlinarith)]
    field_simp; ring
  · have : wL μ a b = 0 := by
      rw [wL, max_eq_right (by nlinarith), zero_div]
    rw [piU, this, ENNReal.ofReal_zero, zero_smul, add_zero]

/-- **Theorem 35, total mass.** `π_U` has total mass `W(U) = (ℓ + r)² / (2 min(ℓ, r))`. -/
theorem piU_univ {μ a b : ℝ} (ha : a < μ) (hb : μ < b) :
    piU μ a b univ = ENNReal.ofReal (W μ a b) := by
  have hβ := two_le_beta ha hb
  have hP : IsProbabilityMeasure (pieceP (beta μ a b)) := pieceP_isProb hβ
  rcases le_or_gt (μ - a) (b - μ) with hle | hlt
  · rw [piU_eq_left ha hb hle, smul_apply, Measure.map_apply (by fun_prop)
      MeasurableSet.univ, preimage_univ, measure_univ, smul_eq_mul, mul_one]
  · rw [piU_eq_right ha hb hlt, smul_apply, Measure.map_apply (by fun_prop)
      MeasurableSet.univ, preimage_univ, measure_univ, smul_eq_mul, mul_one]

lemma wL_nonneg {μ a b : ℝ} (ha : a < μ) : 0 ≤ wL μ a b :=
  div_nonneg (le_max_right _ _) (by linarith)

lemma wR_nonneg {μ a b : ℝ} (hb : μ < b) : 0 ≤ wR μ a b :=
  div_nonneg (le_max_right _ _) (by linarith)

/-- **Theorem 35, mean.** `π_U` has mean `μ`: `∫ x dπ_U(x) = μ · W(U)`. -/
theorem piU_mean {μ a b : ℝ} (ha : a < μ) (hb : μ < b) :
    ∫ x, x ∂(piU μ a b) = μ * W μ a b := by
  have i1 : Integrable (fun x : ℝ => x) (volume.restrict (Icc a b)) :=
    continuous_id.integrableOn_Icc
  have i2 : ∀ (w : ℝ) (e : ℝ),
      Integrable (fun x : ℝ => x) (ENNReal.ofReal w • Measure.dirac e) := fun w e =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [piU, integral_add_measure (i1.add_measure (i2 _ _)) (i2 _ _),
    integral_add_measure i1 (i2 _ _), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_id,
    ENNReal.toReal_ofReal (wL_nonneg ha), ENNReal.toReal_ofReal (wR_nonneg hb), smul_eq_mul,
    smul_eq_mul]
  have hℓ : 0 < μ - a := by linarith
  have hr : 0 < b - μ := by linarith
  rcases le_or_gt (μ - a) (b - μ) with hle | hlt
  · rw [wL, wR, W, min_eq_left hle, max_eq_left (by nlinarith), max_eq_right (by nlinarith)]
    field_simp; ring
  · rw [wL, wR, W, min_eq_right hlt.le, max_eq_right (by nlinarith), max_eq_left (by nlinarith)]
    field_simp; ring

/-! ### Consequences of the decomposition -/

lemma aemeasurable_piU {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} {SA SB : StieltjesFunction ℝ}
    (h : Peel34 f μ A B SA SB) :
    AEMeasurable (fun U => piU μ (A U) (B U)) (volume.restrict (Ioo 0 (f μ))) := by
  refine (measurable_piU μ SA.mono.measurable SB.mono.measurable.neg).aemeasurable.congr
    ((ae_restrict_mem measurableSet_Ioo).mono fun U hU => ?_)
  have hU' : U ∈ Ico 0 (f μ) := ⟨hU.1.le, hU.2⟩
  simp only [Pi.neg_apply, h.SA_eq hU', h.SB_eq hU', neg_neg]

/-- **Theorem 35, (`c:eq:decomp`) for test functions.** For every measurable `φ ≥ 0`,
`∫_0^{f(μ)} π_U(φ) dU = ∫_0^1 φ(x) f(x) dx`. -/
theorem decomp_lintegral {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} {SA SB : StieltjesFunction ℝ}
    (h : Peel34 f μ A B SA SB) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ U in Ioo 0 (f μ), ∫⁻ x, φ x ∂(piU μ (A U) (B U)) =
      ∫⁻ x in Icc 0 1, ENNReal.ofReal (f x) * φ x := by
  rw [← Measure.lintegral_bind (aemeasurable_piU h) hφ.aemeasurable, decomp h,
    lintegral_withDensity_eq_lintegral_mul _
    (show Measurable fun x => ENNReal.ofReal (f x) from
      ENNReal.measurable_ofReal.comp h.cont.measurable) hφ]
  rfl

/-- **Theorem 35, `W` is a density.** `∫_0^{f(μ)} W(U) dU = ∫_0^1 f`, which is `1` when `f` is
a probability density on `[0, 1]`. -/
theorem lintegral_W {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} {SA SB : StieltjesFunction ℝ}
    (h : Peel34 f μ A B SA SB) :
    ∫⁻ U in Ioo 0 (f μ), ENNReal.ofReal (W μ (A U) (B U)) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..1, f x) := by
  have h1 := congrArg (fun m : Measure ℝ => m univ) (decomp h)
  rw [Measure.bind_apply MeasurableSet.univ (aemeasurable_piU h),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hc0 : (0 : ℝ) ∈ Ico 0 (f μ) := ⟨le_rfl, h.pos⟩
  rw [← setLIntegral_congr_fun measurableSet_Ioo fun U hU =>
      piU_univ (h.A_lt U ⟨hU.1.le, hU.2⟩) (h.lt_B U ⟨hU.1.le, hU.2⟩), h1,
    setLIntegral_congr Ioc_ae_eq_Icc.symm, lintegral_Ioc_eq_ofReal h.cont zero_le_one]
  intro t ht
  exact h.lev 0 hc0 t (by rw [h.A0, h.B0]; exact Ioc_subset_Icc_self ht)

/-- With `∫_0^1 f = 1`, `W` is a probability density on `(0, f(μ))`. -/
theorem lintegral_W_eq_one {f : ℝ → ℝ} {μ : ℝ} {A B : ℝ → ℝ} {SA SB : StieltjesFunction ℝ}
    (h : Peel34 f μ A B SA SB) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) :
    ∫⁻ U in Ioo 0 (f μ), ENNReal.ofReal (W μ (A U) (B U)) = 1 := by
  rw [lintegral_W h, hf1, ENNReal.ofReal_one]

end Mixes.Decomp
