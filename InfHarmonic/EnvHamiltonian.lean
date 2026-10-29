import InfHarmonic.EnvSlopeP
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The envelope Hamiltonian `H_f(z) = inf_{ℓ > 0} S_ℓ^+ f(z) ∈ [-∞, ∞)`;
when the forward slopes are nondecreasing in `ℓ` this infimum is their
small-length limit. -/
noncomputable def EnvHamiltonian (f : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) : EReal :=
  ⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeP f l z : ℝ) : EReal)
