import InfHarmonic.QuadEnvP

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The forward envelope slope `S_ℓ^+ f(z) = (P_ℓ f(z) - f(z))/ℓ`. -/
noncomputable def EnvSlopeP (f : WithLp 2 (F × ℝ) → ℝ) (l : ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  (QuadEnvP f l z - f z) / l
