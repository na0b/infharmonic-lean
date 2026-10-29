import InfHarmonic.Preamble
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is affine on space-time. -/
def IsSpaceTimeAffine (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  ∃ (q : F) (b c : ℝ), ∀ z : WithLp 2 (F × ℝ),
    v z = inner ℝ q (ofLp z).1 + b * (ofLp z).2 + c
