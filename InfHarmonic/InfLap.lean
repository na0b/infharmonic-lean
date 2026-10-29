import InfHarmonic.Preamble
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The unnormalized infinity Laplacian `InfLap φ z = D²φ(z)[∇φ(z)]`. -/
noncomputable def InfLap (φ : E → ℝ) (z : E) : ℝ :=
  iteratedFDeriv ℝ 2 φ z (fun _ => ∇ φ z)
