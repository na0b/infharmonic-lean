import InfHarmonic.Preamble
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The forward quadratic envelope `P_ℓ f` of (4.4), with `P_0 f = f`. -/
noncomputable def QuadEnvP (f : WithLp 2 (F × ℝ) → ℝ) (l : ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  if l = 0 then f z else
    sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
