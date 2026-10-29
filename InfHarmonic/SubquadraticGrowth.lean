module

public import InfHarmonic.Preamble

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `f` has subquadratic spatial growth on compact time subintervals of `I`. -/
def SubquadraticGrowth (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  ∀ J ⊆ I, IsCompact J → ∀ ε > 0, ∃ M > 0, ∀ z : WithLp 2 (F × ℝ),
    M ≤ ‖(ofLp z).1‖ → (ofLp z).2 ∈ J → |f z| ≤ ε * ‖(ofLp z).1‖ ^ 2
