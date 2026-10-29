module

public import InfHarmonic.Preamble

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The closed cylinder `Z_λ(z, r; P)` with axis direction `P/‖P‖`, axial
radius `r` and transverse radius `√λ · r`. -/
noncomputable def FitCylinder (z : E) (r lam : ℝ) (P : E) : Set E :=
  {Z | |(inner ℝ (‖P‖⁻¹ • P) (Z - z) : ℝ)| ≤ r ∧
       ‖(Z - z) - (inner ℝ (‖P‖⁻¹ • P) (Z - z) : ℝ) • (‖P‖⁻¹ • P)‖ ≤ Real.sqrt lam * r}
