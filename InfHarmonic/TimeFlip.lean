import InfHarmonic.Preamble
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The time reversal `f̃(x,t) = -f(x,-t)`. -/
noncomputable def TimeFlip (f : WithLp 2 (F × ℝ) → ℝ) : WithLp 2 (F × ℝ) → ℝ  :=
  fun z =>
  -f (toLp 2 ((ofLp z).1, -(ofLp z).2))
