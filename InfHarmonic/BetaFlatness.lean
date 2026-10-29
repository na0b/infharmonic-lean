module

public import InfHarmonic.IsCylinderFit

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `β_u(z, r)`: the supremum of the parameters in `(0,1)` that are not good
for `u` at `(z, r)`, with value `0` when there are none. -/
noncomputable def BetaFlatness (u : E → ℝ) (z : E) (r : ℝ) : ℝ :=
  sSup {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧ ¬ ∃ P : E, IsCylinderFit u z r lam P}
