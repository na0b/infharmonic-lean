import InfHarmonic.Preamble
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `z₀` is a strict maximum point of `φ` on `closedBall z₀ r₁`, then for all small
enough multipliers `p` every maximum point of `w ↦ φ w + ⟪p, w⟫` over `closedBall z₀ r₁`
lies in `ball z₀ ρ`. -/
theorem StrictMaxPerturbLocalization (φ : E → ℝ) (z₀ : E) (r₁ ρ : ℝ)
    (hρ : 0 < ρ) (hρr₁ : ρ ≤ r₁)
    (hφc : ContinuousOn φ (closedBall z₀ r₁))
    (hstrict : ∀ z ∈ closedBall z₀ r₁, z ≠ z₀ → φ z < φ z₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ p : E, ‖p‖ ≤ δ₀ → ∀ z ∈ closedBall z₀ r₁,
      (∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z) →
      ‖z - z₀‖ < ρ := by
  have hr₁ : 0 < r₁ := lt_of_lt_of_le hρ hρr₁
  set S : Set E := closedBall z₀ r₁ \ ball z₀ ρ with hSdef
  have hSmem : ∀ z : E, ‖z - z₀‖ ≤ r₁ → ρ ≤ ‖z - z₀‖ → z ∈ S := by
    intro z h1 h2
    refine ⟨?_, ?_⟩
    · simpa [mem_closedBall, dist_eq_norm] using h1
    · simp only [mem_ball, dist_eq_norm, not_lt]; exact h2
  rcases eq_empty_or_nonempty S with hSe | hSne
  · -- degenerate case: no point of the closed ball sits at distance `≥ ρ` from `z₀`
    refine ⟨1, one_pos, fun p _ z hz _ => ?_⟩
    by_contra hcon
    have hz' : ‖z - z₀‖ ≤ r₁ := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact absurd (hSmem z hz' (not_lt.mp hcon)) (by rw [hSe]; exact notMem_empty z)
  · -- the main case: `S` is a nonempty compact set avoiding `z₀`
    have hScl : IsCompact S := (isCompact_closedBall z₀ r₁).diff isOpen_ball
    have hSsub : S ⊆ closedBall z₀ r₁ := fun z hz => hz.1
    obtain ⟨zm, hzmS, hzmax⟩ := hScl.exists_isMaxOn hSne (hφc.mono hSsub)
    set m : ℝ := φ zm with hm
    have hmlt : m < φ z₀ := by
      refine hstrict zm (hSsub hzmS) ?_
      intro h0
      have hge : ρ ≤ ‖zm - z₀‖ := by
        have h := hzmS.2
        simp only [mem_ball, dist_eq_norm, not_lt] at h
        exact h
      rw [h0] at hge
      simp at hge
      linarith
    refine ⟨(φ z₀ - m) / (2 * r₁), by positivity, fun p hp z hz hmaxz => ?_⟩
    by_contra hcon
    have hz' : ‖z - z₀‖ ≤ r₁ := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hzS : z ∈ S := hSmem z hz' (not_lt.mp hcon)
    have hφz : φ z ≤ m := hzmax hzS
    have hz₀ : z₀ ∈ closedBall z₀ r₁ := by simp [mem_closedBall, hr₁.le]
    have hcmp := hmaxz z₀ hz₀
    have hinner : (inner ℝ p z₀ : ℝ) - inner ℝ p z = - inner ℝ p (z - z₀) := by
      rw [inner_sub_right]; ring
    have hib : (inner ℝ p (z - z₀) : ℝ) ≤ ‖p‖ * ‖z - z₀‖ := real_inner_le_norm _ _
    have hpb : ‖p‖ * ‖z - z₀‖ ≤ (φ z₀ - m) / 2 := by
      have h1 : ‖p‖ * ‖z - z₀‖ ≤ ((φ z₀ - m) / (2 * r₁)) * r₁ :=
        mul_le_mul hp hz' (norm_nonneg _) (by positivity)
      have h2 : ((φ z₀ - m) / (2 * r₁)) * r₁ = (φ z₀ - m) / 2 := by field_simp
      linarith
    linarith
