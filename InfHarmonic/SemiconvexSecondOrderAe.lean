import InfHarmonic.SemiconvexOn
import InfHarmonic.ConvexSecondOrderAe
import InfHarmonic.ConvexLocalExtension
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Alexandrov's theorem for semiconvex functions, in the explicit `δ`-`ρ`
expansion form that the theorem of sums consumes: a `lam`-semiconvex function on
an open convex set has, at almost every point, a second-order Taylor expansion
whose Hessian form is bounded below by `-lam`. -/
theorem SemiconvexSecondOrderAe (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℝ) (hlam : 0 ≤ lam)
    (Ω : Set E) (hΩo : IsOpen Ω) (φ : E → ℝ)
    (hφ : SemiconvexOn lam Ω φ) :
    ∀ᵐ x ∂μ, x ∈ Ω → ∃ (q : E) (A : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ h k : E, A h k = A k h) ∧ (∀ h : E, -(lam * ‖h‖ ^ 2) ≤ A h h) ∧
      ∀ δ > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
        |φ (x + h) - φ x - inner ℝ q h - A h h / 2| ≤ δ * ‖h‖ ^ 2 := by
  -- THE COUNTABLE COVER OF THE .tex IS NOT BUILT BY HAND.  The .tex's Step 1 enumerates rational
  -- balls well inside Ω; in Lean the bad set is LOCALLY null and `measure_null_of_locally_null`
  -- supplies the countable cover from second countability, exactly as in
  -- MoreauProxImageFullMeasure.  Steps 2 and 3 are then unchanged: on one ball
  -- `ConvexLocalExtension` replaces ψ by a globally convex ψ', `ConvexSecondOrderAe` expands ψ',
  -- and the quadratic shift q' = q - lam • z, A' = A - lam • ⟪·,·⟫ turns the expansion of
  -- ψ = φ + lam‖·‖²/2 into one of φ with Hessian bounded below by -lam.
  -- The bundled inner-product form must be BOUND FIRST (`G` below): written inline inside a `-`
  -- the summand elaborates at `E →L⋆[ℝ] E →L[ℝ] ℝ` and the instance fails.
  -- Body-only acknowledgement (trap 3): `hlam` is part of this node's protected signature, but
  -- the route below never needs the SIGN of `lam` -- the Hessian bound A' h h >= -lam‖h‖²
  -- follows from A h h >= 0 alone, for any real `lam`.
  have _ := hlam
  obtain ⟨G, hGapp⟩ : ∃ G : E →L[ℝ] E →L[ℝ] ℝ, ∀ a b : E, G a b = (inner ℝ a b : ℝ) :=
    ⟨innerSL ℝ, fun _ _ => rfl⟩
  -- ψ = φ + lam ‖·‖² / 2 is convex on Ω, by the definition of `SemiconvexOn`
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : E → ℝ, ψ = fun z : E => φ z + lam * ‖z‖ ^ 2 / 2 := ⟨_, rfl⟩
  have hψconv : ConvexOn ℝ Ω ψ := by
    rw [hψdef]
    exact hφ
  obtain ⟨N, hN⟩ : ∃ N : Set E, N = {a : E | ¬ (a ∈ Ω → ∃ (q : E) (A : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ h k : E, A h k = A k h) ∧ (∀ h : E, -(lam * ‖h‖ ^ 2) ≤ A h h) ∧
      ∀ δ > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
        |φ (a + h) - φ a - inner ℝ q h - A h h / 2| ≤ δ * ‖h‖ ^ 2)} := ⟨_, rfl⟩
  rw [MeasureTheory.ae_iff, ← hN]
  refine measure_null_of_locally_null N ?_
  intro x hx
  rw [hN] at hx
  have hxΩ : x ∈ Ω := by
    by_contra hc
    exact hx (fun h => absurd h hc)
  -- a radius with closedBall x (2 r) ⊆ Ω
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.mp hΩo x hxΩ
  obtain ⟨r, hr, hrb⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x (2 * r) ⊆ Ω := by
    refine ⟨ε / 4, by positivity, fun z hz => hballε ?_⟩
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hsub : Metric.ball x r ⊆ Ω := fun z hz =>
    hrb (Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hz))
  -- Step 2: a globally convex function agreeing with ψ on `ball x r`
  obtain ⟨ψ', hψ'conv, hψ'eq⟩ := ConvexLocalExtension Ω hΩo ψ hψconv x r hr hrb
  have hae := ConvexSecondOrderAe μ ψ' hψ'conv
  rw [MeasureTheory.ae_iff] at hae
  refine ⟨N ∩ Metric.ball x r,
    inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)), ?_⟩
  refine measure_mono_null ?_ hae
  -- Step 3: a point of `ball x r` with the ψ'-expansion is NOT in the bad set for φ
  intro z hz hgood
  rw [hN] at hz
  obtain ⟨q, A, hAsym, hApos, hAexp⟩ := hgood
  have hzb : z ∈ Metric.ball x r := hz.2
  obtain ⟨ρ₀, hρ₀, hρ₀b⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hzb
  refine hz.1 (fun _ => ⟨q - lam • z, A - lam • G, ?_, ?_, ?_⟩)
  · -- symmetry of A'
    intro a b
    show A a b - lam * G a b = A b a - lam * G b a
    rw [hAsym a b, hGapp a b, hGapp b a, real_inner_comm a b]
  · -- the Hessian lower bound
    intro h
    show -(lam * ‖h‖ ^ 2) ≤ A h h - lam * G h h
    rw [hGapp h h, real_inner_self_eq_norm_sq h]
    have := hApos h
    linarith
  · -- the expansion, transferred from ψ' to ψ to φ
    intro δ hδ
    obtain ⟨ρ, hρ, hball⟩ := hAexp δ hδ
    refine ⟨min ρ ρ₀, lt_min hρ hρ₀, fun h hh => ?_⟩
    have hh1 : ‖h‖ < ρ := lt_of_lt_of_le hh (min_le_left _ _)
    have hh2 : ‖h‖ < ρ₀ := lt_of_lt_of_le hh (min_le_right _ _)
    -- both z and z + h lie in `ball x r`, so ψ' = ψ at both points
    have hzh : z + h ∈ Metric.ball x r := by
      refine hρ₀b ?_
      rw [Metric.mem_ball, dist_eq_norm, show z + h - z = h from by abel]
      exact hh2
    have e1 : ψ' z = φ z + lam * ‖z‖ ^ 2 / 2 := by
      rw [hψ'eq z hzb, hψdef]
    have e2 : ψ' (z + h) = φ (z + h) + lam * ‖z + h‖ ^ 2 / 2 := by
      rw [hψ'eq (z + h) hzh, hψdef]
    have hb := hball h hh1
    rw [e1, e2] at hb
    -- expand ‖z + h‖² and the shifted jet
    have e3 : ‖z + h‖ ^ 2 = ‖z‖ ^ 2 + 2 * inner ℝ z h + ‖h‖ ^ 2 := norm_add_sq_real z h
    have e4 : (inner ℝ (q - lam • z) h : ℝ) = inner ℝ q h - lam * inner ℝ z h := by
      rw [inner_sub_left, real_inner_smul_left]
    have e5 : (A - lam • G) h h = A h h - lam * ‖h‖ ^ 2 := by
      show A h h - lam * G h h = A h h - lam * ‖h‖ ^ 2
      rw [hGapp h h, real_inner_self_eq_norm_sq h]
    rw [e4, e5]
    rw [e3] at hb
    have hid : φ (z + h) - φ z - (inner ℝ q h - lam * inner ℝ z h)
          - (A h h - lam * ‖h‖ ^ 2) / 2
        = φ (z + h) + lam * (‖z‖ ^ 2 + 2 * inner ℝ z h + ‖h‖ ^ 2) / 2
          - (φ z + lam * ‖z‖ ^ 2 / 2) - inner ℝ q h - A h h / 2 := by
      ring
    rw [hid]
    exact hb
