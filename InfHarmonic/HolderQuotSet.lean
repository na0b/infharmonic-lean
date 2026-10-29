import InfHarmonic.Preamble
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {V : Type*} [NormedAddCommGroup V]

/-- The set of Hölder difference quotients of `g` on `S` at exponent `α`. -/
def HolderQuotSet (g : E → V) (α : ℝ) (S : Set E) : Set ℝ :=
  {q | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α}
