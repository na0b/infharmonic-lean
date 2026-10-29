import InfHarmonic.InfLap
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `u` is a viscosity subsolution of `Δ_∞ u = 0` on the open set `Ω`:
every local upper `C²` test has nonnegative infinity Laplacian. -/
def IsInfSubsolutionOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn u Ω ∧
    ∀ z ∈ Ω, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMaxOn (fun x => u x - φ x) Ω z → 0 ≤ InfLap φ z
