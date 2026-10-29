module

public import InfHarmonic.Preamble

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The second-order superjet `J^{2,+} g (z)`: pairs `(p, X)` with `X`
symmetric and `g (z+h) ≤ g z + ⟪p,h⟫ + X h h / 2 + o(‖h‖²)`. -/
def Superjet (g : E → ℝ) (z : E) : Set (E × (E →L[ℝ] E →L[ℝ] ℝ)) :=
  {pX | (∀ h k : E, pX.2 h k = pX.2 k h) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      g (z + h) ≤ g z + inner ℝ pX.1 h + pX.2 h h / 2 + ε * ‖h‖ ^ 2}
