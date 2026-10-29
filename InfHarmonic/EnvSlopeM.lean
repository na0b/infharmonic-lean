import InfHarmonic.QuadEnvM

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The backward envelope slope `S_ℓ^- f(z) = (f(z) - M_ℓ f(z))/ℓ`. -/
noncomputable def EnvSlopeM (f : WithLp 2 (F × ℝ) → ℝ) (l : ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  (f z - QuadEnvM f l z) / l
