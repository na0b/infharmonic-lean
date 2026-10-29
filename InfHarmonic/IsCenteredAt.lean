import InfHarmonic.IsFit
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is centered at `z_c`: it vanishes there and `(0,0)` is a fit there
of radius one. -/
def IsCenteredAt (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) : Prop :=
  v z = 0 ∧ IsFit C₀ v z 1 0 0
