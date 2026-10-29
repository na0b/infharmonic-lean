import InfHarmonic.HolderQuotSet
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {V : Type*} [NormedAddCommGroup V]

/-- The Hölder seminorm `[g]_{C^{0,α}(S)}`. -/
noncomputable def HolderSeminormOn (g : E → V) (α : ℝ) (S : Set E) : ℝ :=
  sSup (HolderQuotSet g α S)
