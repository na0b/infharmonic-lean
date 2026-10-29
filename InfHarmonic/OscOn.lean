import InfHarmonic.Preamble
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The oscillation `osc_S u = sSup (u '' S) - sInf (u '' S)`. -/
noncomputable def OscOn (u : E → ℝ) (S : Set E) : ℝ :=
  sSup (u '' S) - sInf (u '' S)
