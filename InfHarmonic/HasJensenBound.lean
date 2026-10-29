import InfHarmonic.IsBaryConfig
import InfHarmonic.BaryRadius
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The horizontal Jensen bound (5.2) with constant `κ`, on the time set
`I`. -/
def HasJensenBound (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ) (κ : ℝ) : Prop :=
  ∀ (t : ℝ), t ∈ I → ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
    IsBaryConfig n θ y x →
      (∑ i, θ i * f (toLp 2 (y i, t))) - f (toLp 2 (x, t))
        ≤ κ * BaryRadius n θ y x
