import InfHarmonic.FitCylinder
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `P` realizes the cylinder fit (3.3) of parameter `λ` for `u` at
`(z, r)`. The parameter `λ` is called *good for `u` at `(z,r)`* when such
a `P` exists. -/
def IsCylinderFit (u : E → ℝ) (z : E) (r lam : ℝ) (P : E) : Prop :=
  P ≠ 0 ∧ ∀ Z ∈ FitCylinder z r lam P, |u Z - u z - inner ℝ P (Z - z)| ≤ lam * r
