import InfHarmonic.Preamble
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A sequence of functions with a common subquadratic spatial growth control on
compact time subintervals of `I`. -/
def UnifSubquadraticGrowth (I : Set ℝ) (fs : ℕ → WithLp 2 (F × ℝ) → ℝ) : Prop :=
  ∀ J ⊆ I, IsCompact J → ∀ ε > 0, ∃ M > 0, ∀ (j : ℕ) (z : WithLp 2 (F × ℝ)),
    M ≤ ‖(ofLp z).1‖ → (ofLp z).2 ∈ J → |fs j z| ≤ ε * ‖(ofLp z).1‖ ^ 2
