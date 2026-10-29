import InfHarmonic.Preamble

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `(θ, y)` is a finite horizontal probability configuration with mean `x`. -/
def IsBaryConfig (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F) : Prop :=
  (∀ i, 0 < θ i) ∧ (∑ i, θ i = 1) ∧ (∑ i, θ i • y i = x)
