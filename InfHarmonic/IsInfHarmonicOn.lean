import InfHarmonic.IsInfSubsolutionOn
import InfHarmonic.IsInfSupersolutionOn
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `u` is infinity-harmonic on `Ω`: both viscosity inequalities hold. -/
def IsInfHarmonicOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsInfSubsolutionOn Ω u ∧ IsInfSupersolutionOn Ω u
