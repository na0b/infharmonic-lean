import InfHarmonic.BaryEnv
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The contact envelope `W(x,t) = C_t v(x,t) - κ²t/2` of (5.8). -/
noncomputable def ContactEnv (v : WithLp 2 (F × ℝ) → ℝ) (κ : ℝ)
    (z : WithLp 2 (F × ℝ)) : ℝ :=
  BaryEnv v (ofLp z).2 z - κ ^ 2 * (ofLp z).2 / 2
