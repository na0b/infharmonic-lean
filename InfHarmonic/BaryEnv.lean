module

public import InfHarmonic.IsBaryConfig
public import InfHarmonic.BaryRadius

@[expose] public section
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The barycentric envelope `C_s f` of (5.1). -/
noncomputable def BaryEnv (f : WithLp 2 (F × ℝ) → ℝ) (s : ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  sSup {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
    IsBaryConfig n θ y (ofLp z).1 ∧
    w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
          - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)}
