import InfHarmonic.Preamble
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The upper cone slope `L_r^+(w; z) = r⁻¹ max_{|h| ≤ r} (w (z+h) - w z)`. -/
noncomputable def ConeSlopeUpper (w : E → ℝ) (z : E) (r : ℝ) : ℝ :=
  sSup ((fun h => (w (z + h) - w z) / r) '' closedBall (0 : E) r)
