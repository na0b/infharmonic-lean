module

public import InfHarmonic.IsInfHarmonicOn
public import InfHarmonic.OscOn

@[expose] public section
open Metric Set WithLp

/-- Membership in the normalized lifted family `𝒰` in dimension `d`:
`U(y,b) = u(y) + b` for a continuous infinity-harmonic `u` on `B₁ ⊆ ℝ^d`
with `u 0 = 0` and oscillation at most one. -/
def NormalizedInfFamily (d : ℕ) (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) : Prop :=
  ∃ u : EuclideanSpace ℝ (Fin d) → ℝ,
    IsInfHarmonicOn (ball 0 1) u ∧ u 0 = 0 ∧
    BddAbove (u '' ball 0 1) ∧ BddBelow (u '' ball 0 1) ∧
    OscOn u (ball 0 1) ≤ 1 ∧
    ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), U z = u (ofLp z).1 + (ofLp z).2
