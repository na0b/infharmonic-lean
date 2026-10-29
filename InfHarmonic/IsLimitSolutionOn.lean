import InfHarmonic.IsLimitSubOn
import InfHarmonic.IsLimitSuperOn
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is a viscosity solution of `F[v] = 0` on the open set `Ω`. -/
def IsLimitSolutionOn (Ω : Set (WithLp 2 (F × ℝ))) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsLimitSubOn Ω v ∧ IsLimitSuperOn Ω v
