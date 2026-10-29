import InfHarmonic.Preamble

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The root mean square radius of a finite horizontal configuration about
`x`. -/
noncomputable def BaryRadius (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F) : ℝ :=
  Real.sqrt (∑ i, θ i * ‖y i - x‖ ^ 2)
