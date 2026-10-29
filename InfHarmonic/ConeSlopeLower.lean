module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The lower cone slope `L_r^-(w; z) = r⁻¹ max_{|h| ≤ r} (-(w (z+h) - w z))`. -/
noncomputable def ConeSlopeLower (w : E → ℝ) (z : E) (r : ℝ) : ℝ :=
  sSup ((fun h => (-(w (z + h) - w z)) / r) '' closedBall (0 : E) r)
