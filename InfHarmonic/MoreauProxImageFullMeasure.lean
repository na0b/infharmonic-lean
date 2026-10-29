module

public import InfHarmonic.ProxHitsGradientPoints
public import InfHarmonic.MoreauProxMonotone

@[expose] public section
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Step 3 of Alexandrov's theorem: almost every point of `E` is the proximal
image `u y` of a point `y` at which `u` is differentiable with invertible
derivative; and the range of `u` is dense. -/
theorem MoreauProxImageFullMeasure (μ : Measure E) [μ.IsAddHaarMeasure]
    (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E) (hu : IsMoreauProx ψ u) :
    μ ((u '' {y : E | ∃ P : E →L[ℝ] E, HasFDerivAt u P y ∧
        LinearMap.det (P : E →ₗ[ℝ] E) ≠ 0})ᶜ) = 0 ∧ Dense (Set.range u) := by
  -- THE SET ALGEBRA, recorded here so it is citable by file and line.  With
  --   N = {y | u not differentiable at y},  S = {y | u differentiable at y, det Du y = 0},
  --   G = {y | ∃ P, HasFDerivAt u P y ∧ det P ≠ 0},  D = {x | ψ differentiable at x},
  -- every x ∈ D lies in the range of u (ProxHitsGradientPoints at x with q = ∇ψ x), and its
  -- preimage y there lies in N, S or G; hence
  --   (u '' G)ᶜ ⊆ Dᶜ ∪ u '' N ∪ u '' S,
  -- and the three sets on the right are null for three different reasons: Rademacher for the
  -- locally Lipschitz ψ, the Lipschitz-image bound for u '' N, and the area formula for u '' S.
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's protected
  -- signature; finite-dimensionality is consumed through the Mathlib lemmas below.
  have _ : FiniteDimensional ℝ E := inferInstance
  -- (1) `u` IS 1-LIPSCHITZ, from firm nonexpansiveness with the second term dropped.
  have hunorm : ∀ a b : E, ‖u a - u b‖ ≤ ‖a - b‖ := by
    intro a b
    have h := MoreauProxMonotone ψ hψ a b (u a) (u b) (hu a) (hu b)
    nlinarith [sq_nonneg ‖(a - u a) - (b - u b)‖, norm_nonneg (u a - u b),
      norm_nonneg (a - b)]
  have hulip : LipschitzWith 1 u := by
    intro a b
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (hunorm a b)
  -- (2) μ AND THE n-DIMENSIONAL HAUSDORFF MEASURE ARE MUTUALLY ABSOLUTELY CONTINUOUS.
  -- `μH[n]` is itself an additive Haar measure on `E` (Mathlib instance), and on a second
  -- countable locally compact group every invariant σ-finite measure is absolutely continuous
  -- with respect to a Haar measure; apply that in both directions.  This is the Lean form of
  -- the preamble's "rescaling by the same factor on both sides".
  have hac1 : μ ≪ (μH[(Module.finrank ℝ E : ℝ)] : Measure E) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hac2 : (μH[(Module.finrank ℝ E : ℝ)] : Measure E) ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  -- the preamble's Lipschitz-image bound, specialised to K = 1 and a null source set
  have hnullimg : ∀ A : Set E, μ A = 0 → μ (u '' A) = 0 := by
    intro A hA
    refine hac1 ?_
    have h1 := hulip.hausdorffMeasure_image_le
      (d := (Module.finrank ℝ E : ℝ)) (by positivity) A
    rw [hac2 hA, mul_zero] at h1
    exact le_antisymm h1 zero_le
  -- (3) THE NON-DIFFERENTIABILITY SET OF `u` AND ITS IMAGE ARE NULL (Rademacher).
  have hNnull : μ {y : E | ¬ DifferentiableAt ℝ u y} = 0 :=
    ae_iff.mp (hulip.ae_differentiableAt (μ := μ))
  have huN : μ (u '' {y : E | ¬ DifferentiableAt ℝ u y}) = 0 := hnullimg _ hNnull
  -- (4) THE SINGULAR PART AND ITS IMAGE ARE NULL (area formula).
  -- `fderiv ℝ u` is passed as the TOTAL derivative field the Mathlib lemma wants; on the
  -- differentiability set it agrees with the .tex's `P` by uniqueness of the Fréchet derivative.
  obtain ⟨S, hSdef⟩ : ∃ A : Set E,
      A = {y : E | DifferentiableAt ℝ u y ∧ (fderiv ℝ u y).det = 0} := ⟨_, rfl⟩
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    have hdm : Measurable fun y : E => (fderiv ℝ u y).det :=
      ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ u)
    exact (measurableSet_of_differentiableAt ℝ u).inter (hdm (measurableSet_singleton 0))
  have hSderiv : ∀ y ∈ S, HasFDerivWithinAt u (fderiv ℝ u y) S y := by
    intro y hy
    rw [hSdef] at hy
    exact hy.1.hasFDerivAt.hasFDerivWithinAt
  have huS : μ (u '' S) = 0 := by
    have h := addHaar_image_le_lintegral_abs_det_fderiv μ hSmeas hSderiv
    have heq : Set.EqOn (fun y : E => ENNReal.ofReal |(fderiv ℝ u y).det|)
        (fun _ : E => (0 : ENNReal)) S := by
      intro y hy
      rw [hSdef] at hy
      simp [hy.2]
    have hz : ∫⁻ y in S, ENNReal.ofReal |(fderiv ℝ u y).det| ∂μ = 0 := by
      rw [setLIntegral_congr_fun hSmeas heq, lintegral_zero]
    rw [hz] at h
    exact le_antisymm h zero_le
  -- (5) ALMOST EVERY POINT IS A DIFFERENTIABILITY POINT OF ψ, HENCE IN THE RANGE OF `u`.
  -- ψ is convex and real-valued on all of `E`, hence locally Lipschitz; Rademacher applies on
  -- each ball where it is Lipschitz, and `measure_null_of_locally_null` assembles the countable
  -- cover (second countability) that the preamble's Rademacher clause describes.
  -- TWO LEAN GOTCHAS WORTH RECORDING HERE.  (a) `measure_null_of_locally_null s hs` asks for
  -- `μ u = 0` for some `u ∈ 𝓝[s] x` -- NOT `μ (s ∩ u) = 0` -- so the witness must already be
  -- intersected with `s`, and `inter_mem_nhdsWithin` produces it in the order `s ∩ t` with `s`
  -- the within-set.  (b) the `ℝ≥0∞` notation is scoped and this node's `open` line (which sits
  -- above `-- BODY`) does not bring it in, so the body writes `ENNReal` in full.
  have hψloc : LocallyLipschitz ψ := hψ.locallyLipschitz
  have hDnull : μ {x : E | ¬ DifferentiableAt ℝ ψ x} = 0 := by
    refine measure_null_of_locally_null _ ?_
    intro x _
    obtain ⟨K, t, ht, hlip⟩ := hψloc x
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨{z : E | ¬ DifferentiableAt ℝ ψ z} ∩ Metric.ball x ε,
      inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)), ?_⟩
    have hl2 : LipschitzOnWith K ψ (Metric.ball x ε) := hlip.mono hball
    refine measure_mono_null ?_ (ae_iff.mp (hl2.ae_differentiableWithinAt_of_mem (μ := μ)))
    intro z hz hcon
    exact hz.1 ((hcon hz.2).differentiableAt (Metric.isOpen_ball.mem_nhds hz.2))
  have hDrange : ∀ x : E, DifferentiableAt ℝ ψ x → x ∈ Set.range u := fun x hx =>
    ⟨x + gradient ψ x, ProxHitsGradientPoints ψ hψ u hu x (gradient ψ x) hx.hasGradientAt⟩
  -- (6) THE INCLUSION, AND THE TWO CONCLUSIONS.
  refine ⟨?_, ?_⟩
  · have hincl : (u '' {y : E | ∃ P : E →L[ℝ] E, HasFDerivAt u P y ∧
        LinearMap.det (P : E →ₗ[ℝ] E) ≠ 0})ᶜ ⊆ {x : E | ¬ DifferentiableAt ℝ ψ x} ∪
          (u '' {y : E | ¬ DifferentiableAt ℝ u y} ∪ u '' S) := by
      intro z hz
      by_cases hzd : DifferentiableAt ℝ ψ z
      · obtain ⟨y, hy⟩ := hDrange z hzd
        by_cases hyu : DifferentiableAt ℝ u y
        · refine Or.inr (Or.inr ⟨y, ?_, hy⟩)
          rw [hSdef]
          refine ⟨hyu, ?_⟩
          by_contra hne
          exact hz ⟨y, ⟨fderiv ℝ u y, hyu.hasFDerivAt, hne⟩, hy⟩
        · exact Or.inr (Or.inl ⟨y, hyu, hy⟩)
      · exact Or.inl hzd
    exact measure_mono_null hincl
      (measure_union_null hDnull (measure_union_null huN huS))
  · -- the range is dense: a ball missing it would sit inside the null set `Dᶜ`
    rw [Metric.dense_iff]
    intro x r hr
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Metric.ball x r ⊆ {z : E | ¬ DifferentiableAt ℝ ψ z} := by
      intro z hzb hzd
      have hmem : z ∈ Metric.ball x r ∩ Set.range u := ⟨hzb, hDrange z hzd⟩
      rw [hcon] at hmem
      exact hmem
    exact absurd (measure_mono_null hsub hDnull) (Metric.measure_ball_pos μ x hr).ne'
