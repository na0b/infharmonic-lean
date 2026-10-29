import InfHarmonic.Preamble
set_option linter.unusedSectionVars false
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `z` maximizes `w ↦ φ w + ⟪p, w⟫` over `A`, and `z` has a ball `B(z,η) ⊆ A ∩ Ω`,
then every subgradient `s` on `Ω` of the convexified function
`ψ = φ + lam ‖·‖² / 2` at `z` is forced to equal `lam • z - p`. -/
theorem MaxMultiplierPinsSubgradient (lam : ℝ) (φ : E → ℝ) (A Ω : Set E) (z p s : E)
    (η : ℝ) (hη : 0 < η) (hball : ball z η ⊆ A ∩ Ω)
    (hmax : ∀ w ∈ A, φ w + inner ℝ p w ≤ φ z + inner ℝ p z)
    (hsub : ∀ w ∈ Ω, φ z + lam * ‖z‖ ^ 2 / 2 + inner ℝ s (w - z) ≤ φ w + lam * ‖w‖ ^ 2 / 2) :
    s = lam • z - p := by
  -- the algebraic identity `lam (‖w‖² - ‖z‖²)/2 = lam ⟪z, w - z⟫ + lam ‖w - z‖²/2`
  have hid : ∀ w : E, lam * ‖w‖ ^ 2 / 2 - lam * ‖z‖ ^ 2 / 2
      = lam * inner ℝ z (w - z) + lam * ‖w - z‖ ^ 2 / 2 := by
    intro w
    have h := norm_add_sq_real (w - z) z
    rw [sub_add_cancel] at h
    rw [h, real_inner_comm (w - z) z]
    ring
  set d : E := s - (lam • z - p) with hd
  -- the one-sided estimate on the ball
  have hkey : ∀ w ∈ ball z η, inner ℝ d (w - z) ≤ lam * ‖w - z‖ ^ 2 / 2 := by
    intro w hw
    have hwA : w ∈ A := (hball hw).1
    have hwΩ : w ∈ Ω := (hball hw).2
    have h1 := hmax w hwA
    have h2 := hsub w hwΩ
    have h3 : (inner ℝ p w : ℝ) - inner ℝ p z = inner ℝ p (w - z) := by
      rw [inner_sub_right]
    have h4 : (inner ℝ d (w - z) : ℝ)
        = inner ℝ s (w - z) + inner ℝ p (w - z) - lam * inner ℝ z (w - z) := by
      rw [hd, inner_sub_left, inner_sub_left, real_inner_smul_left]
      ring
    have h5 := hid w
    linarith [h1, h2, h3, h4, h5]
  -- if `d ≠ 0`, test the estimate in the direction `d` with a small step
  by_contra hne
  have hdne : d ≠ 0 := by
    intro h0
    exact hne (by rw [hd] at h0; linear_combination (norm := module) h0)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  set t : ℝ := min (η / (2 * ‖d‖)) (1 / (|lam| + 1)) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ η / (2 * ‖d‖) := min_le_left _ _
  have ht2 : t ≤ 1 / (|lam| + 1) := min_le_right _ _
  have hmem : z + t • d ∈ ball z η := by
    have hn : ‖z + t • d - z‖ = t * ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hhalf : t * ‖d‖ ≤ η / 2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ‖d‖)] at ht1
      linarith
    simp only [mem_ball, dist_eq_norm, hn]
    linarith
  have hstep := hkey _ hmem
  rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hstep
  -- `t‖d‖² ≤ lam t²‖d‖²/2` forces `1 ≤ lam t / 2`, while the choice of `t` gives `lam t / 2 < 1`
  have hP : 0 < t * ‖d‖ ^ 2 := by positivity
  have hone : 1 ≤ lam * t / 2 := by
    refine le_of_mul_le_mul_right ?_ hP
    have heq : (lam * t / 2) * (t * ‖d‖ ^ 2) = lam * (t * ‖d‖) ^ 2 / 2 := by ring
    rw [one_mul, heq]
    exact hstep
  have habs : lam * t / 2 ≤ |lam| * t / 2 := by
    have := le_abs_self lam
    nlinarith [htpos]
  have hlt : |lam| * t / 2 < 1 := by
    have h1 : |lam| * t ≤ |lam| * (1 / (|lam| + 1)) :=
      mul_le_mul_of_nonneg_left ht2 (abs_nonneg lam)
    have h2 : |lam| * (1 / (|lam| + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  linarith
