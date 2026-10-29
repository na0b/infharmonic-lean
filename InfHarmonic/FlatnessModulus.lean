module

public import InfHarmonic.BetaFlatness
public import InfHarmonic.NormalizedInfFamily

@[expose] public section
set_option linter.unusedVariables false
open Metric Set WithLp

/-- The family flatness modulus `b_d(s)` of (3.4): the supremum of
`β_U(z, r)` over the normalized family, centers `z` in `G = B_{3/4}` and
radii `0 < r ≤ s · dist(z, ∂G)`. -/
noncomputable def FlatnessModulus (d : ℕ) (hd : 1 ≤ d) (s : ℝ) : ℝ :=
  sSup {b : ℝ | ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (r : ℝ),
    NormalizedInfFamily d U ∧
    z ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
    0 < r ∧
    r ≤ s * infDist z (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
    b = BetaFlatness U z r}
