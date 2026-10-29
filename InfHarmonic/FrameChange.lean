import InfHarmonic.Preamble
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The sheared change of frame (4.1): based at `z₀`, with scale `R` and
frame parameters `(p₀, a₀)`. -/
noncomputable def FrameChange (v : WithLp 2 (F × ℝ) → ℝ) (z₀ : WithLp 2 (F × ℝ))
    (R : ℝ) (p₀ : F) (a₀ : ℝ) : WithLp 2 (F × ℝ) → ℝ  :=
  fun z =>
  (v (z₀ + toLp 2 (R • ((ofLp z).1 + (ofLp z).2 • p₀), R * (ofLp z).2)) - v z₀) / R
    - inner ℝ p₀ (ofLp z).1 - (a₀ + ‖p₀‖ ^ 2 / 2) * (ofLp z).2
