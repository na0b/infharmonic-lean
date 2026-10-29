import InfHarmonic.IsLimitSolutionOn
import InfHarmonic.IsFit
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Membership in the class `A_{m,C₀}`: an entire solution of the limiting
equation admitting a fit at every center and every positive radius. -/
def IsFitClass (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsLimitSolutionOn Set.univ v ∧
    ∀ (z : WithLp 2 (F × ℝ)) (R : ℝ), 0 < R → ∃ (p : F) (a : ℝ), IsFit C₀ v z R p a
