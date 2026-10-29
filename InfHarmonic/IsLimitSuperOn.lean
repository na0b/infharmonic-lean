import InfHarmonic.LimitOp
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is a viscosity supersolution of `F[v] = 0` on the open set `Ω`. -/
def IsLimitSuperOn (Ω : Set (WithLp 2 (F × ℝ))) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn v Ω ∧
    ∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMinOn (fun w => v w - φ w) Ω z → LimitOp φ z ≤ 0
