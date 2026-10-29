import InfHarmonic.InfLap
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `u` is a viscosity supersolution of `Δ_∞ u = 0` on the open set `Ω`:
every local lower `C²` test has nonpositive infinity Laplacian. -/
def IsInfSupersolutionOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn u Ω ∧
    ∀ z ∈ Ω, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMinOn (fun x => u x - φ x) Ω z → InfLap φ z ≤ 0
