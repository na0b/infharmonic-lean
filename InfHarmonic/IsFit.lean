import InfHarmonic.Preamble
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `(p, a)` is a fit for `v` at `z` of radius `R` with constant `C₀`:
equation (3.2) of the paper, on the sheared box `|l| ≤ R`, `‖h - l • p‖ ≤ R`. -/
def IsFit (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) (R : ℝ)
    (p : F) (a : ℝ) : Prop :=
  ∀ (h : F) (l : ℝ), |l| ≤ R → ‖h - l • p‖ ≤ R →
    |v (z + toLp 2 (h, l)) - v z - inner ℝ p h - (a - ‖p‖ ^ 2 / 2) * l| ≤ C₀ * R
