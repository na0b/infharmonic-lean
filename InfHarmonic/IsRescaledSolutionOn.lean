module

public import InfHarmonic.RescaledOp

@[expose] public section
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is a viscosity solution of `D²v[(∇_x v, 1 + λ v_t)] = 0` on the open
set `Ω`. -/
def IsRescaledSolutionOn (lam : ℝ) (Ω : Set (WithLp 2 (F × ℝ)))
    (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn v Ω ∧
    (∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMaxOn (fun w => v w - φ w) Ω z → 0 ≤ RescaledOp lam φ z) ∧
    (∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMinOn (fun w => v w - φ w) Ω z → RescaledOp lam φ z ≤ 0)
